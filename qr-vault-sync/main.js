/* QR Vault Sync v0.1.0: bundled local-only Obsidian plugin. */
'use strict';
(function(){
const modules=Object.create(null), cache=Object.create(null);
modules["main"]=function(module,exports,require){
'use strict';
const {Plugin, Modal, PluginSettingTab, Setting, Notice, Platform, TFile, TFolder, requestUrl}=require('obsidian');
const {BACKUP_ROOT, DEFAULTS, eligible, planSync, safePath, clampPort, runId, backupPath}=require('./core');
const {randomBytes,b64url,fromBase64,toBase64,hashBytes,importKey,seal,unseal}=require('./crypto');
const {drawQR}=require('./qr');

const NOW=()=>Date.now();
const date=ms=>new Date(ms).toLocaleString();
const errorText=e=>e&&e.message?e.message:String(e);

function isFile(plugin,path){const f=plugin.app.vault.getAbstractFileByPath(path);return f instanceof TFile?f:null;}
async function fileHash(plugin,path) {
  const f=isFile(plugin,path);
  if(!f)return null;
  const data=await plugin.app.vault.readBinary(f);
  return {hash:await hashBytes(data),mtime:f.stat.mtime,size:f.stat.size};
}
async function inventory(plugin){
  const files={},excluded=[];
  const max=plugin.settings.maxFileMB*1024*1024;
  for(const file of plugin.app.vault.getFiles()) {
    if(!eligible(file.path,plugin.settings))continue;
    if(file.stat.size>max){excluded.push(file.path);continue;}
    try {
      const before={mtime:file.stat.mtime,size:file.stat.size};
      const content=await plugin.app.vault.readBinary(file);
      if(file.stat.mtime!==before.mtime||file.stat.size!==before.size){excluded.push(file.path+' (changed during scan)');continue;}
      files[file.path]={hash:await hashBytes(content),mtime:before.mtime,ctime:file.stat.ctime,size:before.size};
    }catch(e){excluded.push(file.path+' ('+errorText(e)+')');}
  }
  return {files,excluded};
}
async function ensureParents(plugin,path) {
  const bits=path.split('/');bits.pop();let current='';
  for(const part of bits){current=current?current+'/'+part:part;
    const existing=plugin.app.vault.getAbstractFileByPath(current);
    if(existing instanceof TFile)throw new Error('A file blocks folder '+current);
    if(!existing) {
      try {await plugin.app.vault.createFolder(current);}catch(e){if(!(plugin.app.vault.getAbstractFileByPath(current) instanceof TFolder))throw e;}
    }
  }
}
async function backupExisting(plugin,path,device,batch) {
  const old=isFile(plugin,path);if(!old)return;
  const dest=backupPath(path,device,batch);
  if(plugin.app.vault.getAbstractFileByPath(dest))throw new Error('Backup destination already exists: '+dest);
  const data=await plugin.app.vault.readBinary(old);
  await ensureParents(plugin,dest);
  await plugin.app.vault.createBinary(dest,data,{ctime:old.stat.ctime,mtime:old.stat.mtime});
}
async function writeToVault(plugin, path, bytes, source, expectedHash, backup,device,batch) {
  if(!eligible(path,plugin.settings))throw new Error('Invalid or excluded path: '+path);
  if(bytes.byteLength>plugin.settings.maxFileMB*1024*1024)throw new Error('File too large: '+path);
  if(await hashBytes(bytes)!==source.hash)throw new Error('Integrity check failed: '+path);
  if(!Number.isFinite(source.mtime)||source.mtime<=0||!Number.isFinite(source.ctime)||source.ctime<=0)throw new Error('Invalid file timestamps');
  let current=isFile(plugin,path);
  if(expectedHash===null){if(plugin.app.vault.getAbstractFileByPath(path))throw new Error('Created meanwhile: '+path);}
  else {if(!current|| (await fileHash(plugin,path)).hash!==expectedHash) throw new Error('Changed meanwhile: '+path);}
  if(backup&&current)await backupExisting(plugin,path,device,batch);
  // Check again after potentially expensive backup, before writing.
  current=isFile(plugin,path);
  if(expectedHash===null){if(plugin.app.vault.getAbstractFileByPath(path))throw new Error('Created meanwhile: '+path);}
  else {if(!current|| (await fileHash(plugin,path)).hash!==expectedHash) throw new Error('Changed while preparing backup: '+path);}
  await ensureParents(plugin,path);
  if(current)await plugin.app.vault.modifyBinary(current,bytes,{mtime:source.mtime,ctime:source.ctime});
  else await plugin.app.vault.createBinary(path,bytes,{mtime:source.mtime,ctime:source.ctime});
}

function localIps(){
  if(!Platform.isDesktopApp)return [];
  const os=require('os');const all=[];
  for(const adapters of Object.values(os.networkInterfaces()))for(const x of adapters||[]) {
    if(x.family==='IPv4'&&!x.internal&&/^\d+\.\d+\.\d+\.\d+$/.test(x.address)&&!all.includes(x.address))all.push(x.address);
  }
  return all.sort((a,b)=>scoreIp(b)-scoreIp(a));
}
function scoreIp(x){return /^(192\.168\.|10\.|172\.(1[6-9]|2\d|3[01])\.)/.test(x)?1:0;}
function isLanAddress(ip) {
  const a=ip.split('.').map(Number);
  return a[0]===10 || a[0]===127 || (a[0]===172&&a[1]>=16&&a[1]<=31) || (a[0]===192&&a[1]===168) || (a[0]===169&&a[1]===254);
}
function encodeLink(ip,port,sid,secret){
  return `obsidian://qr-vault-sync?ip=${encodeURIComponent(ip)}&port=${port}&sid=${sid}&key=${encodeURIComponent(secret)}`;
}
function decodeLink(value) {
  let p;
  if(typeof value==='string') {
    const match=/^obsidian:\/\/qr-vault-sync\?(.*)$/i.exec(value.trim());
    if(!match)throw new Error('Paste a QR Vault Sync pairing link');
    p=Object.fromEntries(new URLSearchParams(match[1]));
  }else p=value;
  if(!p||!/^(\d{1,3}\.){3}\d{1,3}$/.test(p.ip||''))throw new Error('Invalid network address');
  if(p.ip.split('.').some(x=>Number(x)>255)||!isLanAddress(p.ip))throw new Error('Only private local-network addresses are allowed');
  if(!/^[a-f0-9]{24,64}$/i.test(p.sid||''))throw new Error('Invalid pairing session');
  if(!/^[a-zA-Z0-9_-]{43}$/.test(p.key||''))throw new Error('Invalid pairing key');
  const port=Number(p.port);
  if(!Number.isInteger(port)||port<1024||port>65535)throw new Error('Invalid pairing port');
  return {ip:p.ip,port,sid:p.sid,key:p.key};
}

class QRVaultSync extends Plugin {
  async onload(){
    this.settings=Object.assign({},DEFAULTS,await this.loadData());
    this.settings.port=clampPort(this.settings.port);
    this.httpServer=null;this.activePort=null;this.session=null;this.busy=false;
    this.addRibbonIcon('refresh-cw','QR Vault Sync',()=>this.openPanel());
    this.addCommand({id:'show-qr-or-sync',name:'Show pairing QR / Sync vaults',callback:()=>this.openPanel()});
    this.addSettingTab(new QVSSettings(this.app,this));
    this.registerObsidianProtocolHandler('qr-vault-sync',async params=>this.connectAndSync(params));
  }
  onunload(){this.stopServer();}
  async store(){await this.saveData(this.settings);}
  openPanel(){if(Platform.isDesktopApp)new QRPanel(this.app,this).open();else new PhonePanel(this.app,this).open();}
  async startServer(){
    if(!Platform.isDesktopApp)throw new Error('Hosting requires desktop Obsidian');
    if(this.httpServer){this.newSession();return;}
    const http=require('http');
    const server=http.createServer((req,res)=>{this.handleHttp(req,res).catch(e=>{
      console.error('[QR Vault Sync] HTTP error',e);
      if(!res.headersSent){res.writeHead(500,{'content-type':'application/json','cache-control':'no-store'});res.end(JSON.stringify({error:'Request failed'}));}
      else res.end();
    });});
    try {
      await new Promise((resolve,reject)=>{
        const onError=e=>{server.removeListener('listening',onListen);reject(e);};
        const onListen=()=>{server.removeListener('error',onError);resolve();};
        server.once('error',onError);server.once('listening',onListen);
        server.listen(this.settings.port,'0.0.0.0');
      });
    }catch(e){try{server.close();}catch{}throw new Error('Cannot start LAN server on port '+this.settings.port+': '+errorText(e));}
    this.httpServer=server;this.activePort=this.settings.port;this.newSession();
    new Notice('QR Vault Sync: LAN server running. Keep Obsidian open.');
  }
  newSession(){
    this.session={sid:[...randomBytes(18)].map(b=>b.toString(16).padStart(2,'0')).join(''),rawKey:b64url(randomBytes(32)),expires:NOW()+15*60*1000,ivSeen:new Set(),writes:Promise.resolve()};
  }
  stopServer(){if(this.httpServer){try{this.httpServer.close();}catch{}this.httpServer=null;}this.activePort=null;this.session=null;}
  async handleHttp(req,res){
    const reply=(status,payload)=>{res.writeHead(status,{'content-type':'application/json','cache-control':'no-store','x-content-type-options':'nosniff'});res.end(JSON.stringify(payload));};
    if(req.method!=='POST'||req.url!=='/rpc'){reply(404,{error:'Not found'});return;}
    const len=Number(req.headers['content-length']||0);
    if(len>32*1024*1024){reply(413,{error:'Request too large'});return;}
    const chunks=[];let size=0;
    try{for await(const chunk of req){size+=chunk.length;if(size>32*1024*1024)throw new Error('Request too large');chunks.push(chunk);}}
    catch{reply(413,{error:'Request too large'});return;}
    let packet;
    try{packet=JSON.parse(Buffer.concat(chunks).toString('utf8'));}catch{reply(400,{error:'Malformed request'});return;}
    const session=this.session;
    if(!session||session.expires<NOW()||packet.sid!==session.sid){reply(401,{error:'Pairing expired. Scan a new QR code.'});return;}
    if(typeof packet.iv!=='string'||!/^[-_a-zA-Z0-9]{16}$/.test(packet.iv)||session.ivSeen.has(packet.iv)){
      reply(400,{error:'Invalid or repeated request'});return;
    }
    const key=await importKey(session.rawKey);
    let message;
    try{message=await unseal(packet,key);}catch{reply(401,{error:'Unable to decrypt request'});return;}
    session.ivSeen.add(packet.iv);if(session.ivSeen.size>1024)session.ivSeen.delete(session.ivSeen.values().next().value);
    let result;
    try{
      if(!message||typeof message!=='object')throw new Error('Invalid operation');
      if(message.op==='manifest'){
        result={ok:true,...await inventory(this),limit:this.settings.maxFileMB};
      }else if(message.op==='read') {
        if(!eligible(message.path,this.settings)||typeof message.hash!=='string')throw new Error('Invalid file request');
        const f=isFile(this,message.path);if(!f)throw new Error('File missing: '+message.path);
        if(f.stat.size>this.settings.maxFileMB*1024*1024)throw new Error('File too large');
        const bytes=await this.app.vault.readBinary(f);
        const hash=await hashBytes(bytes);if(hash!==message.hash)throw new Error('File changed during sync: '+message.path);
        result={ok:true,data:toBase64(bytes)};
      }else if(message.op==='write') {
        // Serialize remote writes so two simultaneous sync requests cannot race each other.
        const work=async()=>{
          if(!safePath(message.path)||!eligible(message.path,this.settings)||!message.source||typeof message.data!=='string')throw new Error('Invalid write request');
          if(message.data.length>24*1024*1024)throw new Error('File too large');
          if(typeof message.batch!=='string'||!/^\d{4}-[\w-]+$/.test(message.batch))throw new Error('Invalid backup batch');
          const bytes=fromBase64(message.data);
          await writeToVault(this,message.path,bytes,message.source,message.expected===null?null:String(message.expected),!!message.backup,'desktop',message.batch);
          return {ok:true};
        };
        const prior=session.writes;
        const next=prior.then(work);
        session.writes=next.catch(()=>{});
        result=await next;
      }else throw new Error('Unknown operation');
    }catch(e){result={ok:false,error:errorText(e)};}
    if(this.session!==session){reply(401,{error:'Pairing session ended'});return;}
    const sealed=await seal(result,key);
    reply(200,sealed);
  }
  async rpc(pair,message){
    const key=await importKey(pair.key);
    const payload=await seal(message,key);
    let response;
    try{
      response=await requestUrl({url:`http://${pair.ip}:${pair.port}/rpc`,method:'POST',contentType:'application/json',body:JSON.stringify({sid:pair.sid,...payload}),headers:{'Cache-Control':'no-store'}});
    }catch(e){throw new Error('Could not reach desktop. Check both devices are on the same Wi-Fi, desktop firewall, and PC is still showing a valid pairing code. '+errorText(e));}
    if(response.status!==200)throw new Error('Desktop rejected request (HTTP '+response.status+'). Re-scan a fresh QR code.');
    const result=await unseal(response.json,key);
    if(!result.ok)throw new Error(result.error||'Sync request failed');
    return result;
  }
  async connectAndSync(raw){
    if(this.busy){new Notice('A sync is already in progress');return;}
    this.busy=true;
    try{
      const pair=decodeLink(raw);
      const status=new Notice('QR Vault Sync: comparing vaults…',0);
      let remote,local;
      try{
        // Desktop's manifest and phone's files are both hashed before planning.
        remote=await this.rpc(pair,{op:'manifest'});
        local=await inventory(this);
      }finally{status.hide();}
      const plan=planSync(local.files,remote.files);
      const choices=await new PlanPanel(this.app,plan,this.settings.conflictPolicy,local.excluded,remote.excluded,pair.ip).choose();
      if(!choices)return;
      const tasks=[...plan.additions];
      for(const c of plan.conflicts){
        let decision=choices.mode==='individual'?await new ConflictPanel(this.app,c).choose():{from:c.from,backup:choices.mode==='backup'};
        if(!decision)continue;
        if(!decision.from)continue; // Equal/near-equal timestamps require an explicit direction.
        const to=decision.from==='phone'?'desktop':'phone';
        tasks.push({path:c.path,from:decision.from,to,source:c[decision.from],expected:c[to].hash,backup:!!decision.backup});
      }
      const batch=runId();const failed=[];let done=0;
      const progress=new Notice('QR Vault Sync: transferring 0 / '+tasks.length,0);
      try{
        for(const task of tasks){
          try{
            if(task.from==='desktop'){
              const r=await this.rpc(pair,{op:'read',path:task.path,hash:task.source.hash});
              const bytes=fromBase64(r.data);
              await writeToVault(this,task.path,bytes,task.source,task.expected,task.backup,'phone',batch);
            }else{
              const current=isFile(this,task.path);
              if(!current)throw new Error('File missing on phone');
              const bytes=await this.app.vault.readBinary(current);
              if((await hashBytes(bytes))!==task.source.hash)throw new Error('File changed on phone during sync');
              await this.rpc(pair,{op:'write',path:task.path,source:task.source,expected:task.expected,backup:task.backup,batch,data:toBase64(bytes)});
            }
            done++;
          }catch(e){failed.push(`${task.path}: ${errorText(e)}`);}
          progress.setMessage(`QR Vault Sync: transferred ${done} / ${tasks.length}`);
        }
      }finally{progress.hide();}
      new ResultPanel(this.app,{done,total:tasks.length,unchanged:plan.unchanged.length,failed,skipped:plan.conflicts.length - tasks.filter(t=>t.expected!==null).length,excluded:local.excluded.length+remote.excluded.length}).open();
    }catch(e){console.error('[QR Vault Sync]',e);new Notice('QR Vault Sync: '+errorText(e),9000);}
    finally{this.busy=false;}
  }
}

class QRPanel extends Modal{
  constructor(app,plugin){super(app);this.plugin=plugin;this.onIp=null;}
  async onOpen(){
    const c=this.contentEl;c.empty();c.addClass('qvs');c.createEl('h2',{text:'QR Vault Sync'});
    c.createEl('p',{text:'Open this vault in Obsidian on your phone. Scan the code using your phone camera. Both devices must share a local network.'});
    try{await this.plugin.startServer();}
    catch(e){c.createEl('p',{cls:'qvs-error',text:errorText(e)});return;}
    const ips=localIps();if(!ips.length){c.createEl('p',{cls:'qvs-error',text:'No LAN IPv4 address found. Connect the PC to Wi-Fi or Ethernet.'});return;}
    const select=c.createEl('select',{cls:'qvs-ip'});
    for(const ip of ips)select.createEl('option',{text:ip,value:ip,attr:{value:ip}});
    select.value=ips.includes(this.plugin.settings.selectedIP)?this.plugin.settings.selectedIP:ips[0];
    const imageArea=c.createDiv({cls:'qvs-qr-container'});
    const link=c.createEl('textarea',{cls:'qvs-link',attr:{rows:'3',readOnly:'true'}});
    const render=()=>{imageArea.empty();const s=this.plugin.session;const uri=encodeLink(select.value,this.plugin.activePort,s.sid,s.rawKey);
      drawQR(imageArea,uri);link.value=uri;};
    select.addEventListener('change',()=>{this.plugin.settings.selectedIP=select.value;this.plugin.store();render();});
    render();
    const buttons=c.createDiv({cls:'qvs-buttons'});
    new Setting(buttons).addButton(b=>b.setButtonText('Copy pairing link').onClick(()=>{navigator.clipboard.writeText(link.value).then(()=>new Notice('Pairing link copied')).catch(()=>new Notice('Select and copy the link below'));}));
    new Setting(buttons).addButton(b=>b.setButtonText('New QR code').onClick(()=>{this.plugin.newSession();render();new Notice('Old QR code revoked.');}));
    new Setting(buttons).addButton(b=>b.setButtonText('Stop server').onClick(()=>{this.plugin.stopServer();this.close();new Notice('QR Vault Sync stopped.');}));
    c.createEl('p',{cls:'qvs-muted',text:'Pairing expires 15 minutes after code generation. Closing this window keeps the desktop server running; disabling the plugin stops it.'});
  }
  onClose(){this.contentEl.empty();}
}

class PhonePanel extends Modal{
  constructor(app,plugin){super(app);this.plugin=plugin;}
  onOpen(){const c=this.contentEl;c.empty();c.addClass('qvs');c.createEl('h2',{text:'Sync using a QR code'});
    c.createEl('p',{text:'On your PC: Obsidian → QR Vault Sync → Show pairing QR. Scan with your phone camera and tap Open in Obsidian.'});
    c.createEl('p',{text:'If your QR scanner does not open Obsidian, paste the pairing link below.'});
    const input=c.createEl('textarea',{attr:{rows:'4',placeholder:'obsidian://qr-vault-sync?...'},cls:'qvs-link'});
    new Setting(c).addButton(b=>b.setButtonText('Connect & compare').setCta().onClick(async()=>{const link=input.value;this.close();await this.plugin.connectAndSync(link);}));
  }
  onClose(){this.contentEl.empty();}
}

class SelectionModal extends Modal{
  constructor(app){super(app);this._resolve=null;this._answered=false;}
  choose(){return new Promise(resolve=>{this._resolve=resolve;this.open();});}
  finish(value){if(this._answered)return;this._answered=true;this._resolve?.(value);this.close();}
  onClose(){if(!this._answered)this.finish(null);this.contentEl.empty();}
}
class PlanPanel extends SelectionModal{
  constructor(app,plan,policy,excludedLocal,excludedRemote,host){super(app);this.plan=plan;this.policy=policy;this.excludedLocal=excludedLocal;this.excludedRemote=excludedRemote;this.host=host;}
  onOpen(){const c=this.contentEl;c.addClass('qvs');c.createEl('h2',{text:'Review your sync'});
    c.createEl('p',{cls:'qvs-muted',text:`Connected desktop: ${this.host} (local Wi-Fi)`});
    const p=this.plan;
    const table=c.createEl('div',{cls:'qvs-summary'});
    const data=[['New files to copy',p.additions.length],['Different versions to resolve',p.conflicts.length],['Already identical',p.unchanged.length],['Same-time conflicts (need manual choice)',p.conflicts.filter(x=>x.ambiguous).length],['Files excluded / too large',this.excludedLocal.length+this.excludedRemote.length]];
    for(const [label,val] of data){const r=table.createDiv({cls:'qvs-stat'});r.createSpan({text:label});r.createEl('strong',{text:String(val)});}
    c.createEl('p',{cls:'qvs-muted',text:'The newest timestamp wins when versions differ. A hash detects actual differences. Close to equal timestamps are not resolved automatically. Deletions are never propagated.'});
    if(p.conflicts.length){
      c.createEl('h3',{text:'Files with differing versions'});
      const list=c.createDiv({cls:'qvs-conflicts'});
      for(const x of p.conflicts.slice(0,50)){const row=list.createDiv({cls:'qvs-conflict'});row.createEl('strong',{text:x.path});
        row.createEl('small',{text:x.ambiguous?'Similar timestamps — choose manually':`${x.from==='phone'?'Phone':'Desktop'} is newer`});}
      if(p.conflicts.length>50)list.createEl('p',{text:`…and ${p.conflicts.length-50} more`});
      if(this.policy!=='ask')c.createEl('p',{cls:'qvs-muted',text:`Your default setting: ${this.policy==='backup'?'back up older':'replace older'}. Choose an action below.`});
      new Setting(c).addButton(b=>b.setButtonText('Review one by one').setCta().onClick(()=>this.finish({mode:'individual'})));
      new Setting(c).addButton(b=>b.setButtonText('Back up all older versions').onClick(()=>this.finish({mode:'backup'})));
      new Setting(c).addButton(b=>b.setButtonText('Replace all older versions').setWarning().onClick(()=>new DangerPanel(this.app).choose().then(ok=>{if(ok)this.finish({mode:'replace'});}))); 
    }else new Setting(c).addButton(b=>b.setButtonText('Sync now').setCta().onClick(()=>this.finish({mode:'backup'})));
    new Setting(c).addButton(b=>b.setButtonText('Cancel').onClick(()=>this.finish(null)));
  }
}
class DangerPanel extends SelectionModal{
  onOpen(){const c=this.contentEl;c.addClass('qvs');c.createEl('h2',{text:'Replace without backups?'});
    c.createEl('p',{text:'Older versions will be permanently overwritten. To retain copies of the old content, select “Back up all” instead. This cannot be undone by the plugin.'});
    new Setting(c).addButton(b=>b.setButtonText('Yes, replace older versions').setWarning().onClick(()=>this.finish(true)));
    new Setting(c).addButton(b=>b.setButtonText('Cancel').onClick(()=>this.finish(false)));
  }
}
class ConflictPanel extends SelectionModal{
  constructor(app,item){super(app);this.item=item;}
  onOpen(){const c=this.contentEl;c.addClass('qvs');const x=this.item;
    c.createEl('h2',{text:'Choose a version'});c.createEl('h3',{text:x.path});
    c.createEl('p',{text:`Phone: ${date(x.phone.mtime)}  •  ${x.phone.size} bytes`});
    c.createEl('p',{text:`Desktop: ${date(x.desktop.mtime)}  •  ${x.desktop.size} bytes`});
    if(x.ambiguous){c.createEl('p',{cls:'qvs-error',text:'Timestamps are too close to choose reliably. Pick which device should win.'});
      for(const from of ['phone','desktop']){
        new Setting(c).addButton(b=>b.setButtonText(`Use ${from} (back up other version)`).onClick(()=>this.finish({from,backup:true})));
        new Setting(c).addButton(b=>b.setButtonText(`Use ${from} (replace other version)`).setWarning().onClick(()=>this.finish({from,backup:false})));
      }
    }else {
      c.createEl('p',{text:`Newest version is on ${x.from}.`});
      new Setting(c).addButton(b=>b.setButtonText('Keep newest + back up older').setCta().onClick(()=>this.finish({from:x.from,backup:true})));
      new Setting(c).addButton(b=>b.setButtonText('Keep newest + replace older').setWarning().onClick(()=>this.finish({from:x.from,backup:false})));
    }
    new Setting(c).addButton(b=>b.setButtonText('Skip this file').onClick(()=>this.finish(null)));
  }
}
class ResultPanel extends Modal{
  constructor(app,data){super(app);this.data=data;}
  onOpen(){const c=this.contentEl;c.addClass('qvs');c.createEl('h2',{text:'Sync finished'});
    const x=this.data;c.createEl('p',{text:`${x.done} / ${x.total} files transferred. ${x.unchanged} already identical. ${x.skipped} conflicting files skipped. ${x.excluded} excluded or too large.`});
    if(x.failed.length){c.createEl('p',{cls:'qvs-error',text:`${x.failed.length} files failed (not overwritten):`});const box=c.createEl('pre',{cls:'qvs-errors'});box.setText(x.failed.join('\n'));}
    else c.createEl('p',{text:'No transfer errors reported.'});
    c.createEl('p',{text:`Older copies, when selected, are stored in “${BACKUP_ROOT}”.`});
    new Setting(c).addButton(b=>b.setButtonText('Done').setCta().onClick(()=>this.close()));
  }
  onClose(){this.contentEl.empty();}
}
class QVSSettings extends PluginSettingTab{
  constructor(app,plugin){super(app,plugin);this.plugin=plugin;}
  display(){const c=this.containerEl;c.empty();c.createEl('h2',{text:'QR Vault Sync'});
    c.createEl('p',{text:'Private, local-Wi-Fi sync. No cloud account. Install on both your PC and phone. PC hosts; phone scans and starts sync.'});
    new Setting(c).setName('Open sync panel').setDesc('Desktop: show a QR code. Mobile: paste a pairing link if camera scanning fails.')
      .addButton(b=>b.setButtonText('Open').onClick(()=>this.plugin.openPanel()));
    new Setting(c).setName('Default conflict behavior').setDesc('A run always asks for final approval; choose per-file, replace all, or back up all.')
      .addDropdown(d=>d.addOption('ask','Ask for each file').addOption('backup','Prefer backup all').addOption('replace','Prefer replace all').setValue(this.plugin.settings.conflictPolicy).onChange(async v=>{this.plugin.settings.conflictPolicy=v;await this.plugin.store();}));
    new Setting(c).setName('Include attachments').setDesc('Sync images, PDFs, canvas files and other vault files, as well as Markdown.')
      .addToggle(t=>t.setValue(this.plugin.settings.includeAttachments).onChange(async v=>{this.plugin.settings.includeAttachments=v;await this.plugin.store();}));
    new Setting(c).setName('Maximum file size (MB)').setDesc('Larger files are skipped to limit mobile memory. Defaults to 8 MB.')
      .addText(t=>t.setValue(String(this.plugin.settings.maxFileMB)).onChange(async v=>{const n=Number(v);if(Number.isFinite(n)&&n>=1&&n<=16){this.plugin.settings.maxFileMB=n;await this.plugin.store();}}));
    new Setting(c).setName('Exclude folders').setDesc('One relative vault folder per line; QR Sync Backups and .obsidian are always excluded.')
      .addTextArea(t=>t.setPlaceholder('Private\nArchive').setValue(this.plugin.settings.exclusions).onChange(async v=>{this.plugin.settings.exclusions=v;await this.plugin.store();}));
    new Setting(c).setName('Backup folder').setDesc('Always “'+BACKUP_ROOT+'” at the root of each vault. Excluded from all transfers.');
    if(Platform.isDesktopApp){
      new Setting(c).setName('PC server port').setDesc('Change this only if necessary. Restart the server to apply changes.')
        .addText(t=>t.setValue(String(this.plugin.settings.port)).onChange(async v=>{const n=Number(v);if(Number.isInteger(n)&&n>=1024&&n<=65535){this.plugin.settings.port=n;await this.plugin.store();}}));
      new Setting(c).setName('Stop sharing').setDesc('Stop listening on your local network and invalidate the QR code.')
        .addButton(b=>b.setButtonText('Stop server').onClick(()=>{this.plugin.stopServer();new Notice('LAN server stopped.');}));
    }
    c.createEl('p',{cls:'qvs-muted',text:'Security: QR pairing uses an expiring random AES-256-GCM key. Keep the QR code private. The server listens on your LAN until stopped or Obsidian closes. Firewalls may ask to allow Obsidian on private networks.'});
  }
}
module.exports=QRVaultSync;
module.exports.__testing={inventory,writeToVault,backupExisting,decodeLink,encodeLink,ensureParents,fileHash,QRVaultSync};

};
modules["core"]=function(module,exports,require){
'use strict';

const BACKUP_ROOT = 'QR Sync Backups';
const MAX_CLOCK_SKEW_MS = 2000;
const DEFAULTS = Object.freeze({
  port: 43177,
  conflictPolicy: 'ask',
  includeAttachments: true,
  maxFileMB: 8,
  exclusions: '',
  selectedIP: '',
});

function safePath(path) {
  if (typeof path !== 'string' || !path || path.length > 1024 || path.includes('\\') || path.startsWith('/') || /[\u0000-\u001f]/.test(path)) return false;
  if (path.split('/').some(part => !part || part === '.' || part === '..' || part.startsWith('.'))) return false;
  if (path.split('/').some(part => /[:*?"<>|]/.test(part))) return false;
  return true;
}

function within(path, folder) { return path === folder || path.startsWith(folder + '/'); }

function eligible(path, settings) {
  if (!safePath(path) || within(path, BACKUP_ROOT) || within(path, '.obsidian')) return false;
  if (settings.includeAttachments === false && !path.toLowerCase().endsWith('.md')) return false;
  const exclusions = (settings.exclusions || '').split(/[\n,]/).map(x => x.trim().replace(/\/+$/, '')).filter(Boolean);
  if (exclusions.some(dir => within(path, dir))) return false;
  return true;
}

function planSync(phone, desktop) {
  const all = new Set([...Object.keys(phone), ...Object.keys(desktop)]);
  const additions = [], conflicts = [], unchanged = [];
  for (const path of [...all].sort((a,b)=>a.localeCompare(b))) {
    const a=phone[path], b=desktop[path];
    if (!a || !b) {
      additions.push({path, from:a?'phone':'desktop', to:a?'desktop':'phone', source:a||b, expected:null});
      continue;
    }
    if (a.hash===b.hash) {unchanged.push(path);continue;}
    const diff=a.mtime-b.mtime;
    conflicts.push({path, phone:a, desktop:b, from:Math.abs(diff)<=MAX_CLOCK_SKEW_MS?null:diff>0?'phone':'desktop', ambiguous:Math.abs(diff)<=MAX_CLOCK_SKEW_MS});
  }
  return { additions, conflicts, unchanged };
}

function clampPort(n) {
  n=Number(n);
  return Number.isInteger(n)&&n>=1024&&n<=65535?n:DEFAULTS.port;
}

function runId() {return new Date().toISOString().replace(/[:.]/g,'-')+'-'+Math.random().toString(36).slice(2,8);}

function backupPath(path, device, batch) {
  if (!safePath(path) || !/^[a-z0-9-]+$/i.test(batch) || !/^(phone|desktop)$/.test(device)) throw new Error('Invalid backup path');
  return `${BACKUP_ROOT}/${batch}/${device}/${path}`;
}

function sameEntry(a,b) {return (!a&&!b)||!!(a&&b&&a.hash===b.hash&&a.mtime===b.mtime&&a.size===b.size);}

module.exports={BACKUP_ROOT,DEFAULTS,MAX_CLOCK_SKEW_MS,safePath,eligible,planSync,clampPort,runId,backupPath,sameEntry};

};
modules["crypto"]=function(module,exports,require){
'use strict';

function webCrypto() {
  if (globalThis.crypto && globalThis.crypto.subtle) return globalThis.crypto;
  // Desktop-only fallback. Never imported when the plugin loads on mobile.
  if (typeof require === 'function') return require('crypto').webcrypto;
  throw new Error('Secure cryptography is unavailable');
}
function randomBytes(length) {const a=new Uint8Array(length);webCrypto().getRandomValues(a);return a;}
function toBase64(input) {
  const u=input instanceof Uint8Array?input:new Uint8Array(input);
  let s='';const stride=8192;
  for (let i=0;i<u.length;i+=stride) s+=String.fromCharCode.apply(null,u.subarray(i,i+stride));
  return btoa(s);
}
function fromBase64(s) {const b=atob(s);const u=new Uint8Array(b.length);for(let i=0;i<b.length;i++)u[i]=b.charCodeAt(i);return u;}
function b64url(buf) {return toBase64(buf).replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,'');}
function fromB64url(s) {return fromBase64(s.replace(/-/g,'+').replace(/_/g,'/')+'='.repeat((4-s.length%4)%4));}
async function hashBytes(buf) {return b64url(new Uint8Array(await webCrypto().subtle.digest('SHA-256',buf)));}
async function importKey(key) {return webCrypto().subtle.importKey('raw',fromB64url(key),'AES-GCM',false,['encrypt','decrypt']);}
async function seal(payload,key) {
  const iv=randomBytes(12);
  const buf=new TextEncoder().encode(JSON.stringify(payload));
  const encrypted=await webCrypto().subtle.encrypt({name:'AES-GCM',iv},key,buf);
  return {iv:b64url(iv), data:b64url(new Uint8Array(encrypted))};
}
async function unseal(packet,key) {
  if (!packet||typeof packet.iv!=='string'||typeof packet.data!=='string') throw new Error('Invalid encrypted envelope');
  const clear=await webCrypto().subtle.decrypt({name:'AES-GCM',iv:fromB64url(packet.iv)},key,fromB64url(packet.data));
  return JSON.parse(new TextDecoder().decode(clear));
}
module.exports={webCrypto,randomBytes,toBase64,fromBase64,b64url,fromB64url,hashBytes,importKey,seal,unseal};

};
modules["qr"]=function(module,exports,require){
'use strict';
// Kazuhiko Arase QRCode encoder (MIT), vendored under src/vendor/QRCode.
const QRCode=require('./vendor/QRCode/index');
const Level=require('./vendor/QRCode/QRErrorCorrectLevel');
function drawQR(el, value) {
  const qr=new QRCode(-1,Level.M);
  qr.addData(value);qr.make();
  const n=qr.getModuleCount(), quiet=4, scale=6;
  const canvas=el.createEl('canvas',{cls:'qvs-qr',attr:{'aria-label':'Pairing QR code'}});
  const size=(n+2*quiet)*scale;canvas.width=canvas.height=size;
  const ctx=canvas.getContext('2d');
  ctx.fillStyle='#fff';ctx.fillRect(0,0,size,size);ctx.fillStyle='#111';
  for(let y=0;y<n;y++)for(let x=0;x<n;x++)if(qr.isDark(y,x))ctx.fillRect((x+quiet)*scale,(y+quiet)*scale,scale,scale);
  return canvas;
}
module.exports={drawQR};

};
modules["vendor/QRCode/index"]=function(module,exports,require){
//---------------------------------------------------------------------
// QRCode for JavaScript
//
// Copyright (c) 2009 Kazuhiko Arase
//
// URL: http://www.d-project.com/
//
// Licensed under the MIT license:
//   http://www.opensource.org/licenses/mit-license.php
//
// The word "QR Code" is registered trademark of 
// DENSO WAVE INCORPORATED
//   http://www.denso-wave.com/qrcode/faqpatent-e.html
//
//---------------------------------------------------------------------
// Modified to work in node for this project (and some refactoring)
//---------------------------------------------------------------------

var QR8bitByte = require('./QR8bitByte');
var QRUtil = require('./QRUtil');
var QRPolynomial = require('./QRPolynomial');
var QRRSBlock = require('./QRRSBlock');
var QRBitBuffer = require('./QRBitBuffer');

function QRCode(typeNumber, errorCorrectLevel) {
	this.typeNumber = typeNumber;
	this.errorCorrectLevel = errorCorrectLevel;
	this.modules = null;
	this.moduleCount = 0;
	this.dataCache = null;
	this.dataList = [];
}

QRCode.prototype = {
	
	addData : function(data) {
		var newData = new QR8bitByte(data);
		this.dataList.push(newData);
		this.dataCache = null;
	},
	
	isDark : function(row, col) {
		if (row < 0 || this.moduleCount <= row || col < 0 || this.moduleCount <= col) {
			throw new Error(row + "," + col);
		}
		return this.modules[row][col];
	},

	getModuleCount : function() {
		return this.moduleCount;
	},
	
	make : function() {
		// Calculate automatically typeNumber if provided is < 1
		if (this.typeNumber < 1 ){
			var typeNumber = 1;
			for (typeNumber = 1; typeNumber < 40; typeNumber++) {
				var rsBlocks = QRRSBlock.getRSBlocks(typeNumber, this.errorCorrectLevel);

				var buffer = new QRBitBuffer();
				var totalDataCount = 0;
				for (var i = 0; i < rsBlocks.length; i++) {
					totalDataCount += rsBlocks[i].dataCount;
				}

				for (var x = 0; x < this.dataList.length; x++) {
					var data = this.dataList[x];
					buffer.put(data.mode, 4);
					buffer.put(data.getLength(), QRUtil.getLengthInBits(data.mode, typeNumber) );
					data.write(buffer);
				}
				if (buffer.getLengthInBits() <= totalDataCount * 8)
					break;
			}
			this.typeNumber = typeNumber;
		}
		this.makeImpl(false, this.getBestMaskPattern() );
	},
	
	makeImpl : function(test, maskPattern) {
		
		this.moduleCount = this.typeNumber * 4 + 17;
		this.modules = new Array(this.moduleCount);
		
		for (var row = 0; row < this.moduleCount; row++) {
			
			this.modules[row] = new Array(this.moduleCount);
			
			for (var col = 0; col < this.moduleCount; col++) {
				this.modules[row][col] = null;//(col + row) % 3;
			}
		}
	
		this.setupPositionProbePattern(0, 0);
		this.setupPositionProbePattern(this.moduleCount - 7, 0);
		this.setupPositionProbePattern(0, this.moduleCount - 7);
		this.setupPositionAdjustPattern();
		this.setupTimingPattern();
		this.setupTypeInfo(test, maskPattern);
		
		if (this.typeNumber >= 7) {
			this.setupTypeNumber(test);
		}
	
		if (this.dataCache === null) {
			this.dataCache = QRCode.createData(this.typeNumber, this.errorCorrectLevel, this.dataList);
		}
	
		this.mapData(this.dataCache, maskPattern);
	},

	setupPositionProbePattern : function(row, col)  {
		
		for (var r = -1; r <= 7; r++) {
			
			if (row + r <= -1 || this.moduleCount <= row + r) continue;
			
			for (var c = -1; c <= 7; c++) {
				
				if (col + c <= -1 || this.moduleCount <= col + c) continue;
				
				if ( (0 <= r && r <= 6 && (c === 0 || c === 6) ) || 
                     (0 <= c && c <= 6 && (r === 0 || r === 6) ) || 
                     (2 <= r && r <= 4 && 2 <= c && c <= 4) ) {
					this.modules[row + r][col + c] = true;
				} else {
					this.modules[row + r][col + c] = false;
				}
			}		
		}		
	},
	
	getBestMaskPattern : function() {
	
		var minLostPoint = 0;
		var pattern = 0;
	
		for (var i = 0; i < 8; i++) {
			
			this.makeImpl(true, i);
	
			var lostPoint = QRUtil.getLostPoint(this);
	
			if (i === 0 || minLostPoint >  lostPoint) {
				minLostPoint = lostPoint;
				pattern = i;
			}
		}
	
		return pattern;
	},
	
	createMovieClip : function(target_mc, instance_name, depth) {
	
		var qr_mc = target_mc.createEmptyMovieClip(instance_name, depth);
		var cs = 1;
	
		this.make();

		for (var row = 0; row < this.modules.length; row++) {
			
			var y = row * cs;
			
			for (var col = 0; col < this.modules[row].length; col++) {
	
				var x = col * cs;
				var dark = this.modules[row][col];
			
				if (dark) {
					qr_mc.beginFill(0, 100);
					qr_mc.moveTo(x, y);
					qr_mc.lineTo(x + cs, y);
					qr_mc.lineTo(x + cs, y + cs);
					qr_mc.lineTo(x, y + cs);
					qr_mc.endFill();
				}
			}
		}
		
		return qr_mc;
	},

	setupTimingPattern : function() {
		
		for (var r = 8; r < this.moduleCount - 8; r++) {
			if (this.modules[r][6] !== null) {
				continue;
			}
			this.modules[r][6] = (r % 2 === 0);
		}
	
		for (var c = 8; c < this.moduleCount - 8; c++) {
			if (this.modules[6][c] !== null) {
				continue;
			}
			this.modules[6][c] = (c % 2 === 0);
		}
	},
	
	setupPositionAdjustPattern : function() {
	
		var pos = QRUtil.getPatternPosition(this.typeNumber);
		
		for (var i = 0; i < pos.length; i++) {
		
			for (var j = 0; j < pos.length; j++) {
			
				var row = pos[i];
				var col = pos[j];
				
				if (this.modules[row][col] !== null) {
					continue;
				}
				
				for (var r = -2; r <= 2; r++) {
				
					for (var c = -2; c <= 2; c++) {
					
						if (Math.abs(r) === 2 || 
                            Math.abs(c) === 2 ||
                            (r === 0 && c === 0) ) {
							this.modules[row + r][col + c] = true;
						} else {
							this.modules[row + r][col + c] = false;
						}
					}
				}
			}
		}
	},
	
	setupTypeNumber : function(test) {
	
		var bits = QRUtil.getBCHTypeNumber(this.typeNumber);
        var mod;
	
		for (var i = 0; i < 18; i++) {
			mod = (!test && ( (bits >> i) & 1) === 1);
			this.modules[Math.floor(i / 3)][i % 3 + this.moduleCount - 8 - 3] = mod;
		}
	
		for (var x = 0; x < 18; x++) {
			mod = (!test && ( (bits >> x) & 1) === 1);
			this.modules[x % 3 + this.moduleCount - 8 - 3][Math.floor(x / 3)] = mod;
		}
	},
	
	setupTypeInfo : function(test, maskPattern) {
	
		var data = (this.errorCorrectLevel << 3) | maskPattern;
		var bits = QRUtil.getBCHTypeInfo(data);
        var mod;
	
		// vertical		
		for (var v = 0; v < 15; v++) {
	
			mod = (!test && ( (bits >> v) & 1) === 1);
	
			if (v < 6) {
				this.modules[v][8] = mod;
			} else if (v < 8) {
				this.modules[v + 1][8] = mod;
			} else {
				this.modules[this.moduleCount - 15 + v][8] = mod;
			}
		}
	
		// horizontal
		for (var h = 0; h < 15; h++) {
	
			mod = (!test && ( (bits >> h) & 1) === 1);
			
			if (h < 8) {
				this.modules[8][this.moduleCount - h - 1] = mod;
			} else if (h < 9) {
				this.modules[8][15 - h - 1 + 1] = mod;
			} else {
				this.modules[8][15 - h - 1] = mod;
			}
		}
	
		// fixed module
		this.modules[this.moduleCount - 8][8] = (!test);
	
	},
	
	mapData : function(data, maskPattern) {
		
		var inc = -1;
		var row = this.moduleCount - 1;
		var bitIndex = 7;
		var byteIndex = 0;
		
		for (var col = this.moduleCount - 1; col > 0; col -= 2) {
	
			if (col === 6) col--;
	
			while (true) {
	
				for (var c = 0; c < 2; c++) {
					
					if (this.modules[row][col - c] === null) {
						
						var dark = false;
	
						if (byteIndex < data.length) {
							dark = ( ( (data[byteIndex] >>> bitIndex) & 1) === 1);
						}
	
						var mask = QRUtil.getMask(maskPattern, row, col - c);
	
						if (mask) {
							dark = !dark;
						}
						
						this.modules[row][col - c] = dark;
						bitIndex--;
	
						if (bitIndex === -1) {
							byteIndex++;
							bitIndex = 7;
						}
					}
				}
								
				row += inc;
	
				if (row < 0 || this.moduleCount <= row) {
					row -= inc;
					inc = -inc;
					break;
				}
			}
		}
		
	}

};

QRCode.PAD0 = 0xEC;
QRCode.PAD1 = 0x11;

QRCode.createData = function(typeNumber, errorCorrectLevel, dataList) {
	
	var rsBlocks = QRRSBlock.getRSBlocks(typeNumber, errorCorrectLevel);
	
	var buffer = new QRBitBuffer();
	
	for (var i = 0; i < dataList.length; i++) {
		var data = dataList[i];
		buffer.put(data.mode, 4);
		buffer.put(data.getLength(), QRUtil.getLengthInBits(data.mode, typeNumber) );
		data.write(buffer);
	}

	// calc num max data.
	var totalDataCount = 0;
	for (var x = 0; x < rsBlocks.length; x++) {
		totalDataCount += rsBlocks[x].dataCount;
	}

	if (buffer.getLengthInBits() > totalDataCount * 8) {
		throw new Error("code length overflow. (" + 
            buffer.getLengthInBits() + 
            ">" +  
            totalDataCount * 8 + 
            ")");
	}

	// end code
	if (buffer.getLengthInBits() + 4 <= totalDataCount * 8) {
		buffer.put(0, 4);
	}

	// padding
	while (buffer.getLengthInBits() % 8 !== 0) {
		buffer.putBit(false);
	}

	// padding
	while (true) {
		
		if (buffer.getLengthInBits() >= totalDataCount * 8) {
			break;
		}
		buffer.put(QRCode.PAD0, 8);
		
		if (buffer.getLengthInBits() >= totalDataCount * 8) {
			break;
		}
		buffer.put(QRCode.PAD1, 8);
	}

	return QRCode.createBytes(buffer, rsBlocks);
};

QRCode.createBytes = function(buffer, rsBlocks) {

	var offset = 0;
	
	var maxDcCount = 0;
	var maxEcCount = 0;
	
	var dcdata = new Array(rsBlocks.length);
	var ecdata = new Array(rsBlocks.length);
	
	for (var r = 0; r < rsBlocks.length; r++) {

		var dcCount = rsBlocks[r].dataCount;
		var ecCount = rsBlocks[r].totalCount - dcCount;

		maxDcCount = Math.max(maxDcCount, dcCount);
		maxEcCount = Math.max(maxEcCount, ecCount);
		
		dcdata[r] = new Array(dcCount);
		
		for (var i = 0; i < dcdata[r].length; i++) {
			dcdata[r][i] = 0xff & buffer.buffer[i + offset];
		}
		offset += dcCount;
		
		var rsPoly = QRUtil.getErrorCorrectPolynomial(ecCount);
		var rawPoly = new QRPolynomial(dcdata[r], rsPoly.getLength() - 1);

		var modPoly = rawPoly.mod(rsPoly);
		ecdata[r] = new Array(rsPoly.getLength() - 1);
		for (var x = 0; x < ecdata[r].length; x++) {
            var modIndex = x + modPoly.getLength() - ecdata[r].length;
			ecdata[r][x] = (modIndex >= 0)? modPoly.get(modIndex) : 0;
		}

	}
	
	var totalCodeCount = 0;
	for (var y = 0; y < rsBlocks.length; y++) {
		totalCodeCount += rsBlocks[y].totalCount;
	}

	var data = new Array(totalCodeCount);
	var index = 0;

	for (var z = 0; z < maxDcCount; z++) {
		for (var s = 0; s < rsBlocks.length; s++) {
			if (z < dcdata[s].length) {
				data[index++] = dcdata[s][z];
			}
		}
	}

	for (var xx = 0; xx < maxEcCount; xx++) {
		for (var t = 0; t < rsBlocks.length; t++) {
			if (xx < ecdata[t].length) {
				data[index++] = ecdata[t][xx];
			}
		}
	}

	return data;

};

module.exports = QRCode;

};
modules["vendor/QRCode/QR8bitByte"]=function(module,exports,require){
var QRMode = require('./QRMode');

function QR8bitByte(data) {
	this.mode = QRMode.MODE_8BIT_BYTE;
	this.data = data;
}

QR8bitByte.prototype = {

	getLength : function() {
		return this.data.length;
	},
	
	write : function(buffer) {
		for (var i = 0; i < this.data.length; i++) {
			// not JIS ...
			buffer.put(this.data.charCodeAt(i), 8);
		}
	}
};

module.exports = QR8bitByte;

};
modules["vendor/QRCode/QRMode"]=function(module,exports,require){
module.exports = {
    MODE_NUMBER :       1 << 0,
    MODE_ALPHA_NUM :    1 << 1,
    MODE_8BIT_BYTE :    1 << 2,
    MODE_KANJI :        1 << 3
};

};
modules["vendor/QRCode/QRUtil"]=function(module,exports,require){
var QRMode = require('./QRMode');
var QRPolynomial = require('./QRPolynomial');
var QRMath = require('./QRMath');
var QRMaskPattern = require('./QRMaskPattern');

var QRUtil = {

    PATTERN_POSITION_TABLE : [
        [],
        [6, 18],
        [6, 22],
        [6, 26],
        [6, 30],
        [6, 34],
        [6, 22, 38],
        [6, 24, 42],
        [6, 26, 46],
        [6, 28, 50],
        [6, 30, 54],        
        [6, 32, 58],
        [6, 34, 62],
        [6, 26, 46, 66],
        [6, 26, 48, 70],
        [6, 26, 50, 74],
        [6, 30, 54, 78],
        [6, 30, 56, 82],
        [6, 30, 58, 86],
        [6, 34, 62, 90],
        [6, 28, 50, 72, 94],
        [6, 26, 50, 74, 98],
        [6, 30, 54, 78, 102],
        [6, 28, 54, 80, 106],
        [6, 32, 58, 84, 110],
        [6, 30, 58, 86, 114],
        [6, 34, 62, 90, 118],
        [6, 26, 50, 74, 98, 122],
        [6, 30, 54, 78, 102, 126],
        [6, 26, 52, 78, 104, 130],
        [6, 30, 56, 82, 108, 134],
        [6, 34, 60, 86, 112, 138],
        [6, 30, 58, 86, 114, 142],
        [6, 34, 62, 90, 118, 146],
        [6, 30, 54, 78, 102, 126, 150],
        [6, 24, 50, 76, 102, 128, 154],
        [6, 28, 54, 80, 106, 132, 158],
        [6, 32, 58, 84, 110, 136, 162],
        [6, 26, 54, 82, 110, 138, 166],
        [6, 30, 58, 86, 114, 142, 170]
    ],

    G15 : (1 << 10) | (1 << 8) | (1 << 5) | (1 << 4) | (1 << 2) | (1 << 1) | (1 << 0),
    G18 : (1 << 12) | (1 << 11) | (1 << 10) | (1 << 9) | (1 << 8) | (1 << 5) | (1 << 2) | (1 << 0),
    G15_MASK : (1 << 14) | (1 << 12) | (1 << 10)    | (1 << 4) | (1 << 1),

    getBCHTypeInfo : function(data) {
        var d = data << 10;
        while (QRUtil.getBCHDigit(d) - QRUtil.getBCHDigit(QRUtil.G15) >= 0) {
            d ^= (QRUtil.G15 << (QRUtil.getBCHDigit(d) - QRUtil.getBCHDigit(QRUtil.G15) ) );    
        }
        return ( (data << 10) | d) ^ QRUtil.G15_MASK;
    },

    getBCHTypeNumber : function(data) {
        var d = data << 12;
        while (QRUtil.getBCHDigit(d) - QRUtil.getBCHDigit(QRUtil.G18) >= 0) {
            d ^= (QRUtil.G18 << (QRUtil.getBCHDigit(d) - QRUtil.getBCHDigit(QRUtil.G18) ) );    
        }
        return (data << 12) | d;
    },

    getBCHDigit : function(data) {

        var digit = 0;

        while (data !== 0) {
            digit++;
            data >>>= 1;
        }

        return digit;
    },

    getPatternPosition : function(typeNumber) {
        return QRUtil.PATTERN_POSITION_TABLE[typeNumber - 1];
    },

    getMask : function(maskPattern, i, j) {
        
        switch (maskPattern) {
            
        case QRMaskPattern.PATTERN000 : return (i + j) % 2 === 0;
        case QRMaskPattern.PATTERN001 : return i % 2 === 0;
        case QRMaskPattern.PATTERN010 : return j % 3 === 0;
        case QRMaskPattern.PATTERN011 : return (i + j) % 3 === 0;
        case QRMaskPattern.PATTERN100 : return (Math.floor(i / 2) + Math.floor(j / 3) ) % 2 === 0;
        case QRMaskPattern.PATTERN101 : return (i * j) % 2 + (i * j) % 3 === 0;
        case QRMaskPattern.PATTERN110 : return ( (i * j) % 2 + (i * j) % 3) % 2 === 0;
        case QRMaskPattern.PATTERN111 : return ( (i * j) % 3 + (i + j) % 2) % 2 === 0;

        default :
            throw new Error("bad maskPattern:" + maskPattern);
        }
    },

    getErrorCorrectPolynomial : function(errorCorrectLength) {

        var a = new QRPolynomial([1], 0);

        for (var i = 0; i < errorCorrectLength; i++) {
            a = a.multiply(new QRPolynomial([1, QRMath.gexp(i)], 0) );
        }

        return a;
    },

    getLengthInBits : function(mode, type) {

        if (1 <= type && type < 10) {

            // 1 - 9

            switch(mode) {
            case QRMode.MODE_NUMBER     : return 10;
            case QRMode.MODE_ALPHA_NUM  : return 9;
            case QRMode.MODE_8BIT_BYTE  : return 8;
            case QRMode.MODE_KANJI      : return 8;
            default :
                throw new Error("mode:" + mode);
            }

        } else if (type < 27) {

            // 10 - 26

            switch(mode) {
            case QRMode.MODE_NUMBER     : return 12;
            case QRMode.MODE_ALPHA_NUM  : return 11;
            case QRMode.MODE_8BIT_BYTE  : return 16;
            case QRMode.MODE_KANJI      : return 10;
            default :
                throw new Error("mode:" + mode);
            }

        } else if (type < 41) {

            // 27 - 40

            switch(mode) {
            case QRMode.MODE_NUMBER     : return 14;
            case QRMode.MODE_ALPHA_NUM  : return 13;
            case QRMode.MODE_8BIT_BYTE  : return 16;
            case QRMode.MODE_KANJI      : return 12;
            default :
                throw new Error("mode:" + mode);
            }

        } else {
            throw new Error("type:" + type);
        }
    },

    getLostPoint : function(qrCode) {
        
        var moduleCount = qrCode.getModuleCount();
        var lostPoint = 0;
        var row = 0; 
        var col = 0;

        
        // LEVEL1
        
        for (row = 0; row < moduleCount; row++) {

            for (col = 0; col < moduleCount; col++) {

                var sameCount = 0;
                var dark = qrCode.isDark(row, col);

                for (var r = -1; r <= 1; r++) {

                    if (row + r < 0 || moduleCount <= row + r) {
                        continue;
                    }

                    for (var c = -1; c <= 1; c++) {

                        if (col + c < 0 || moduleCount <= col + c) {
                            continue;
                        }

                        if (r === 0 && c === 0) {
                            continue;
                        }

                        if (dark === qrCode.isDark(row + r, col + c) ) {
                            sameCount++;
                        }
                    }
                }

                if (sameCount > 5) {
                    lostPoint += (3 + sameCount - 5);
                }
            }
        }

        // LEVEL2

        for (row = 0; row < moduleCount - 1; row++) {
            for (col = 0; col < moduleCount - 1; col++) {
                var count = 0;
                if (qrCode.isDark(row,     col    ) ) count++;
                if (qrCode.isDark(row + 1, col    ) ) count++;
                if (qrCode.isDark(row,     col + 1) ) count++;
                if (qrCode.isDark(row + 1, col + 1) ) count++;
                if (count === 0 || count === 4) {
                    lostPoint += 3;
                }
            }
        }

        // LEVEL3

        for (row = 0; row < moduleCount; row++) {
            for (col = 0; col < moduleCount - 6; col++) {
                if (qrCode.isDark(row, col) && 
                        !qrCode.isDark(row, col + 1) && 
                         qrCode.isDark(row, col + 2) && 
                         qrCode.isDark(row, col + 3) && 
                         qrCode.isDark(row, col + 4) && 
                        !qrCode.isDark(row, col + 5) && 
                         qrCode.isDark(row, col + 6) ) {
                    lostPoint += 40;
                }
            }
        }

        for (col = 0; col < moduleCount; col++) {
            for (row = 0; row < moduleCount - 6; row++) {
                if (qrCode.isDark(row, col) &&
                        !qrCode.isDark(row + 1, col) &&
                         qrCode.isDark(row + 2, col) &&
                         qrCode.isDark(row + 3, col) &&
                         qrCode.isDark(row + 4, col) &&
                        !qrCode.isDark(row + 5, col) &&
                         qrCode.isDark(row + 6, col) ) {
                    lostPoint += 40;
                }
            }
        }

        // LEVEL4
        
        var darkCount = 0;

        for (col = 0; col < moduleCount; col++) {
            for (row = 0; row < moduleCount; row++) {
                if (qrCode.isDark(row, col) ) {
                    darkCount++;
                }
            }
        }
        
        var ratio = Math.abs(100 * darkCount / moduleCount / moduleCount - 50) / 5;
        lostPoint += ratio * 10;

        return lostPoint;       
    }

};

module.exports = QRUtil;

};
modules["vendor/QRCode/QRPolynomial"]=function(module,exports,require){
var QRMath = require('./QRMath');

function QRPolynomial(num, shift) {
	if (num.length === undefined) {
		throw new Error(num.length + "/" + shift);
	}

	var offset = 0;

	while (offset < num.length && num[offset] === 0) {
		offset++;
	}

	this.num = new Array(num.length - offset + shift);
	for (var i = 0; i < num.length - offset; i++) {
		this.num[i] = num[i + offset];
	}
}

QRPolynomial.prototype = {

	get : function(index) {
		return this.num[index];
	},
	
	getLength : function() {
		return this.num.length;
	},
	
	multiply : function(e) {
	
		var num = new Array(this.getLength() + e.getLength() - 1);
	
		for (var i = 0; i < this.getLength(); i++) {
			for (var j = 0; j < e.getLength(); j++) {
				num[i + j] ^= QRMath.gexp(QRMath.glog(this.get(i) ) + QRMath.glog(e.get(j) ) );
			}
		}
	
		return new QRPolynomial(num, 0);
	},
	
	mod : function(e) {
	
		if (this.getLength() - e.getLength() < 0) {
			return this;
		}
	
		var ratio = QRMath.glog(this.get(0) ) - QRMath.glog(e.get(0) );
	
		var num = new Array(this.getLength() );
		
		for (var i = 0; i < this.getLength(); i++) {
			num[i] = this.get(i);
		}
		
		for (var x = 0; x < e.getLength(); x++) {
			num[x] ^= QRMath.gexp(QRMath.glog(e.get(x) ) + ratio);
		}
	
		// recursive call
		return new QRPolynomial(num, 0).mod(e);
	}
};

module.exports = QRPolynomial;

};
modules["vendor/QRCode/QRMath"]=function(module,exports,require){
var QRMath = {

	glog : function(n) {
	
		if (n < 1) {
			throw new Error("glog(" + n + ")");
		}
		
		return QRMath.LOG_TABLE[n];
	},
	
	gexp : function(n) {
	
		while (n < 0) {
			n += 255;
		}
	
		while (n >= 256) {
			n -= 255;
		}
	
		return QRMath.EXP_TABLE[n];
	},
	
	EXP_TABLE : new Array(256),
	
	LOG_TABLE : new Array(256)

};
	
for (var i = 0; i < 8; i++) {
	QRMath.EXP_TABLE[i] = 1 << i;
}
for (var i = 8; i < 256; i++) {
	QRMath.EXP_TABLE[i] = QRMath.EXP_TABLE[i - 4]
		^ QRMath.EXP_TABLE[i - 5]
		^ QRMath.EXP_TABLE[i - 6]
		^ QRMath.EXP_TABLE[i - 8];
}
for (var i = 0; i < 255; i++) {
	QRMath.LOG_TABLE[QRMath.EXP_TABLE[i] ] = i;
}

module.exports = QRMath;

};
modules["vendor/QRCode/QRMaskPattern"]=function(module,exports,require){
module.exports = {
	PATTERN000 : 0,
	PATTERN001 : 1,
	PATTERN010 : 2,
	PATTERN011 : 3,
	PATTERN100 : 4,
	PATTERN101 : 5,
	PATTERN110 : 6,
	PATTERN111 : 7
};

};
modules["vendor/QRCode/QRRSBlock"]=function(module,exports,require){
var QRErrorCorrectLevel = require('./QRErrorCorrectLevel');

function QRRSBlock(totalCount, dataCount) {
	this.totalCount = totalCount;
	this.dataCount  = dataCount;
}

QRRSBlock.RS_BLOCK_TABLE = [

	// L
	// M
	// Q
	// H

	// 1
	[1, 26, 19],
	[1, 26, 16],
	[1, 26, 13],
	[1, 26, 9],
	
	// 2
	[1, 44, 34],
	[1, 44, 28],
	[1, 44, 22],
	[1, 44, 16],

	// 3
	[1, 70, 55],
	[1, 70, 44],
	[2, 35, 17],
	[2, 35, 13],

	// 4		
	[1, 100, 80],
	[2, 50, 32],
	[2, 50, 24],
	[4, 25, 9],
	
	// 5
	[1, 134, 108],
	[2, 67, 43],
	[2, 33, 15, 2, 34, 16],
	[2, 33, 11, 2, 34, 12],
	
	// 6
	[2, 86, 68],
	[4, 43, 27],
	[4, 43, 19],
	[4, 43, 15],
	
	// 7		
	[2, 98, 78],
	[4, 49, 31],
	[2, 32, 14, 4, 33, 15],
	[4, 39, 13, 1, 40, 14],
	
	// 8
	[2, 121, 97],
	[2, 60, 38, 2, 61, 39],
	[4, 40, 18, 2, 41, 19],
	[4, 40, 14, 2, 41, 15],
	
	// 9
	[2, 146, 116],
	[3, 58, 36, 2, 59, 37],
	[4, 36, 16, 4, 37, 17],
	[4, 36, 12, 4, 37, 13],
	
	// 10		
	[2, 86, 68, 2, 87, 69],
	[4, 69, 43, 1, 70, 44],
	[6, 43, 19, 2, 44, 20],
	[6, 43, 15, 2, 44, 16],

	// 11
	[4, 101, 81],
	[1, 80, 50, 4, 81, 51],
	[4, 50, 22, 4, 51, 23],
	[3, 36, 12, 8, 37, 13],

	// 12
	[2, 116, 92, 2, 117, 93],
	[6, 58, 36, 2, 59, 37],
	[4, 46, 20, 6, 47, 21],
	[7, 42, 14, 4, 43, 15],

	// 13
	[4, 133, 107],
	[8, 59, 37, 1, 60, 38],
	[8, 44, 20, 4, 45, 21],
	[12, 33, 11, 4, 34, 12],

	// 14
	[3, 145, 115, 1, 146, 116],
	[4, 64, 40, 5, 65, 41],
	[11, 36, 16, 5, 37, 17],
	[11, 36, 12, 5, 37, 13],

	// 15
	[5, 109, 87, 1, 110, 88],
	[5, 65, 41, 5, 66, 42],
	[5, 54, 24, 7, 55, 25],
	[11, 36, 12],

	// 16
	[5, 122, 98, 1, 123, 99],
	[7, 73, 45, 3, 74, 46],
	[15, 43, 19, 2, 44, 20],
	[3, 45, 15, 13, 46, 16],

	// 17
	[1, 135, 107, 5, 136, 108],
	[10, 74, 46, 1, 75, 47],
	[1, 50, 22, 15, 51, 23],
	[2, 42, 14, 17, 43, 15],

	// 18
	[5, 150, 120, 1, 151, 121],
	[9, 69, 43, 4, 70, 44],
	[17, 50, 22, 1, 51, 23],
	[2, 42, 14, 19, 43, 15],

	// 19
	[3, 141, 113, 4, 142, 114],
	[3, 70, 44, 11, 71, 45],
	[17, 47, 21, 4, 48, 22],
	[9, 39, 13, 16, 40, 14],

	// 20
	[3, 135, 107, 5, 136, 108],
	[3, 67, 41, 13, 68, 42],
	[15, 54, 24, 5, 55, 25],
	[15, 43, 15, 10, 44, 16],

	// 21
	[4, 144, 116, 4, 145, 117],
	[17, 68, 42],
	[17, 50, 22, 6, 51, 23],
	[19, 46, 16, 6, 47, 17],

	// 22
	[2, 139, 111, 7, 140, 112],
	[17, 74, 46],
	[7, 54, 24, 16, 55, 25],
	[34, 37, 13],

	// 23
	[4, 151, 121, 5, 152, 122],
	[4, 75, 47, 14, 76, 48],
	[11, 54, 24, 14, 55, 25],
	[16, 45, 15, 14, 46, 16],

	// 24
	[6, 147, 117, 4, 148, 118],
	[6, 73, 45, 14, 74, 46],
	[11, 54, 24, 16, 55, 25],
	[30, 46, 16, 2, 47, 17],

	// 25
	[8, 132, 106, 4, 133, 107],
	[8, 75, 47, 13, 76, 48],
	[7, 54, 24, 22, 55, 25],
	[22, 45, 15, 13, 46, 16],

	// 26
	[10, 142, 114, 2, 143, 115],
	[19, 74, 46, 4, 75, 47],
	[28, 50, 22, 6, 51, 23],
	[33, 46, 16, 4, 47, 17],

	// 27
	[8, 152, 122, 4, 153, 123],
	[22, 73, 45, 3, 74, 46],
	[8, 53, 23, 26, 54, 24],
	[12, 45, 15, 28, 46, 16],

	// 28
	[3, 147, 117, 10, 148, 118],
	[3, 73, 45, 23, 74, 46],
	[4, 54, 24, 31, 55, 25],
	[11, 45, 15, 31, 46, 16],

	// 29
	[7, 146, 116, 7, 147, 117],
	[21, 73, 45, 7, 74, 46],
	[1, 53, 23, 37, 54, 24],
	[19, 45, 15, 26, 46, 16],

	// 30
	[5, 145, 115, 10, 146, 116],
	[19, 75, 47, 10, 76, 48],
	[15, 54, 24, 25, 55, 25],
	[23, 45, 15, 25, 46, 16],

	// 31
	[13, 145, 115, 3, 146, 116],
	[2, 74, 46, 29, 75, 47],
	[42, 54, 24, 1, 55, 25],
	[23, 45, 15, 28, 46, 16],

	// 32
	[17, 145, 115],
	[10, 74, 46, 23, 75, 47],
	[10, 54, 24, 35, 55, 25],
	[19, 45, 15, 35, 46, 16],

	// 33
	[17, 145, 115, 1, 146, 116],
	[14, 74, 46, 21, 75, 47],
	[29, 54, 24, 19, 55, 25],
	[11, 45, 15, 46, 46, 16],

	// 34
	[13, 145, 115, 6, 146, 116],
	[14, 74, 46, 23, 75, 47],
	[44, 54, 24, 7, 55, 25],
	[59, 46, 16, 1, 47, 17],

	// 35
	[12, 151, 121, 7, 152, 122],
	[12, 75, 47, 26, 76, 48],
	[39, 54, 24, 14, 55, 25],
	[22, 45, 15, 41, 46, 16],

	// 36
	[6, 151, 121, 14, 152, 122],
	[6, 75, 47, 34, 76, 48],
	[46, 54, 24, 10, 55, 25],
	[2, 45, 15, 64, 46, 16],

	// 37
	[17, 152, 122, 4, 153, 123],
	[29, 74, 46, 14, 75, 47],
	[49, 54, 24, 10, 55, 25],
	[24, 45, 15, 46, 46, 16],

	// 38
	[4, 152, 122, 18, 153, 123],
	[13, 74, 46, 32, 75, 47],
	[48, 54, 24, 14, 55, 25],
	[42, 45, 15, 32, 46, 16],

	// 39
	[20, 147, 117, 4, 148, 118],
	[40, 75, 47, 7, 76, 48],
	[43, 54, 24, 22, 55, 25],
	[10, 45, 15, 67, 46, 16],

	// 40
	[19, 148, 118, 6, 149, 119],
	[18, 75, 47, 31, 76, 48],
	[34, 54, 24, 34, 55, 25],
	[20, 45, 15, 61, 46, 16]
];

QRRSBlock.getRSBlocks = function(typeNumber, errorCorrectLevel) {
	
	var rsBlock = QRRSBlock.getRsBlockTable(typeNumber, errorCorrectLevel);
	
	if (rsBlock === undefined) {
		throw new Error("bad rs block @ typeNumber:" + typeNumber + "/errorCorrectLevel:" + errorCorrectLevel);
	}

	var length = rsBlock.length / 3;
	
	var list = [];
	
	for (var i = 0; i < length; i++) {

		var count = rsBlock[i * 3 + 0];
		var totalCount = rsBlock[i * 3 + 1];
		var dataCount  = rsBlock[i * 3 + 2];

		for (var j = 0; j < count; j++) {
			list.push(new QRRSBlock(totalCount, dataCount) );	
		}
	}
	
	return list;
};

QRRSBlock.getRsBlockTable = function(typeNumber, errorCorrectLevel) {

	switch(errorCorrectLevel) {
	case QRErrorCorrectLevel.L :
		return QRRSBlock.RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 0];
	case QRErrorCorrectLevel.M :
		return QRRSBlock.RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 1];
	case QRErrorCorrectLevel.Q :
		return QRRSBlock.RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 2];
	case QRErrorCorrectLevel.H :
		return QRRSBlock.RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 3];
	default :
		return undefined;
	}
};

module.exports = QRRSBlock;

};
modules["vendor/QRCode/QRErrorCorrectLevel"]=function(module,exports,require){
module.exports = {
	L : 1,
	M : 0,
	Q : 3,
	H : 2
};


};
modules["vendor/QRCode/QRBitBuffer"]=function(module,exports,require){
function QRBitBuffer() {
	this.buffer = [];
	this.length = 0;
}

QRBitBuffer.prototype = {

	get : function(index) {
		var bufIndex = Math.floor(index / 8);
		return ( (this.buffer[bufIndex] >>> (7 - index % 8) ) & 1) == 1;
	},
	
	put : function(num, length) {
		for (var i = 0; i < length; i++) {
			this.putBit( ( (num >>> (length - i - 1) ) & 1) == 1);
		}
	},
	
	getLengthInBits : function() {
		return this.length;
	},
	
	putBit : function(bit) {
	
		var bufIndex = Math.floor(this.length / 8);
		if (this.buffer.length <= bufIndex) {
			this.buffer.push(0);
		}
	
		if (bit) {
			this.buffer[bufIndex] |= (0x80 >>> (this.length % 8) );
		}
	
		this.length++;
	}
};

module.exports = QRBitBuffer;

};
function internal(id){if(cache[id])return cache[id].exports;const factory=modules[id];if(!factory) return require(id);const mod={exports:{}};cache[id]=mod;const relative=(name)=>{if(!name.startsWith('.'))return require(name);const parts=id.split('/');parts.pop();for(const bit of name.split('/')){if(bit==='..')parts.pop();else if(bit!=='.')parts.push(bit);}return internal(parts.join('/'));};factory(mod,mod.exports,relative);return mod.exports;}
module.exports=internal('main');
})();
