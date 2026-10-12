PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; connect-src 'none'; img-src 'none'; base-uri 'none'; form-action 'none'">
<title>BeeJSP · Discovery</title>
<style>
:root{color-scheme:dark;--ink:#edf3f7;--muted:#b2c1cf;--line:#415162;--accent:#79ddd2;--paper:#10161d;--surface:#18212b;--hover:#243543}
*{box-sizing:border-box}body{margin:0;background:var(--paper);color:var(--ink);font:15px/1.5 system-ui,sans-serif}
header,main{max-width:1600px;margin:auto;padding:24px 32px}header{border-bottom:1px solid var(--line)}
.eyebrow{font-size:12px;letter-spacing:.15em;text-transform:uppercase;color:var(--accent);font-weight:700}
h1{font-size:36px;margin:5px 0}h2{font-size:20px}h3{font-size:16px}p{margin:8px 0}.muted{color:var(--muted)}
.cards{display:flex;flex-wrap:wrap;gap:12px;margin:22px 0}
.card{background:var(--surface);border:1px solid var(--line);border-radius:8px;padding:14px 20px;min-width:150px}.card b{display:block;font-size:28px}
.controls{display:flex;flex-wrap:wrap;gap:12px;margin:16px 0}label{display:flex;flex-direction:column;font-size:12px;color:var(--muted);gap:4px;min-width:0;max-width:100%}
input,select,button{font:inherit;color:var(--ink);background:var(--surface);border:1px solid var(--line);border-radius:5px;padding:8px;max-width:100%}
input{min-width:260px}button{cursor:pointer}button:hover,a:hover{color:var(--accent);background:var(--hover)}:focus-visible{outline:3px solid var(--accent);outline-offset:3px}th[aria-sort='ascending'],th[aria-sort='descending']{background:var(--hover)}tbody tr:hover{background:var(--hover)}button:disabled{opacity:.45;cursor:default}
a{color:var(--accent);overflow-wrap:anywhere}.table-wrap{overflow-x:auto;background:var(--surface);border:1px solid var(--line);border-radius:8px}
table{border-collapse:collapse;width:100%;font-size:13px}th,td{text-align:left;border-bottom:1px solid var(--line);padding:12px;vertical-align:top}
th{background:#21303d;white-space:nowrap}th button{border:0;background:transparent;padding:0;font-weight:700}td:first-child{min-width:270px}
.identity{font-weight:700}.title{display:block;margin-top:4px}.badge{font-size:11px;font-weight:700;white-space:nowrap}.CONTESTED,.UNKNOWN{color:#ffcf83}
nav{display:flex;align-items:center;gap:12px;flex-wrap:wrap;margin:18px 0}dialog{width:min(1100px,95vw);max-height:90vh;border:1px solid var(--line);border-radius:10px;padding:24px;background:var(--surface);color:var(--ink)}
dialog::backdrop{background:#102a3288}dialog .close{float:right}pre{white-space:pre-wrap;overflow-wrap:anywhere;font:13px/1.6 ui-monospace,monospace;background:var(--paper);padding:12px}
.field{border-bottom:1px solid var(--line);padding:8px 0;white-space:pre-wrap;overflow-wrap:anywhere}.field strong{display:block;color:var(--muted);font-size:12px}
details{border:1px solid var(--line);border-radius:6px;padding:12px;margin:10px 0}summary{cursor:pointer;font-weight:600}.provenance{overflow-wrap:anywhere}
@media(max-width:700px){header,main{padding:18px 14px}h1{font-size:28px}.card{flex:1;min-width:120px}input{min-width:0;width:100%}}
</style>
</head>
<body>
<header><div class="eyebrow">BeeJSP / Research workspace</div><h1>Mathematics worth formalizing.</h1><p class="muted">Explore the complete JSP catalog and its recorded evidence. Every candidate requires mathematical review.</p></header>
<main>
<p id="freshness" class="muted" aria-label="Snapshot freshness"></p>
<section id="kpis" class="cards" aria-label="Overview"></section>
<div class="controls">
<label>Search catalog and evidence<input id="search" type="search" placeholder="JSP ID, title, author, theorem…"></label>
<label>Rows per page<select id="page-size"><option>25</option><option>50</option><option>100</option></select></label>
</div>
<div id="filters" class="controls"></div>
<button id="reset">Reset search and filters</button>
<p id="results" role="status" aria-live="polite"></p>
<div class="table-wrap"><table><thead><tr id="columns"></tr></thead><tbody id="rows"></tbody></table></div>
<nav aria-label="Pagination"><button id="previous">Previous</button><span id="page"></span><button id="next">Next</button></nav>
<p class="muted">Lean status is recorded by the official catalog. Activity is not proof verification; awards are not confirmed payment.</p>
</main>
<dialog id="detail" aria-labelledby="detail-title"><button class="close" id="close">Close</button><div id="detail-body"></div></dialog>
<noscript>This dashboard requires local JavaScript for exploration. The saved snapshot JSON and CSV contain all records and evidence.</noscript>
<script type="application/json" id="discovery-data">__DISCOVERY_DATA__</script>
<script>
'use strict';
const data=JSON.parse(document.getElementById('discovery-data').textContent);
const byId=id=>document.getElementById(id);
const element=(tag,text,cls)=>{const n=document.createElement(tag);if(text!==undefined)n.textContent=String(text);if(cls)n.className=cls;return n;};
const show=value=>value===null||value===undefined?'unknown':typeof value==='object'?JSON.stringify(value,null,2):String(value);
const field=(parent,label,value)=>{const n=element('div',undefined,'field');n.append(element('strong',label),element('span',show(value)));parent.append(n);};
const link=(href,label)=>{const a=element('a',label||href);a.href=href;a.target='_blank';a.rel='noopener noreferrer';a.referrerPolicy='no-referrer';return a;};
const awardLabels={announced:'Award announced',candidate:'Candidate registered',none_in_scope:'No award recorded',unknown:'Unknown'};
const proofLabels={source_linked:'Source linked',claimed:'Claimed',partial:'Partial',invalid:'Invalid',reproduced:'Reproduced',independently_verified:'Independently verified',unresolved:'Unresolved'};
const stateLabels={...awardLabels,...proofLabels,CONTESTED:'Contested',VERIFIED:'Verified',REVIEWED:'Reviewed',NONE_IN_SCOPE:'None in scope',UNKNOWN:'Unknown',open:'Open',closed:'Closed',merged:'Merged','closed-unmerged':'Closed, unmerged',exact_jsp_id:'Exact JSP ID',evidence_backed_erdos_alias:'Reviewed Erdős alias',supplementary_title:'Uncertain title match',lean:'Lean submission',mathematical:'Mathematical submission',administrative:'Administrative',other:'Other'};
const humanState=value=>stateLabels[value]??String(value).replaceAll('_',' ').replace(/^./,c=>c.toUpperCase());
const humanEvidence=value=>Array.isArray(value)?value.map(humanEvidence):value&&typeof value==='object'?Object.fromEntries(Object.entries(value).map(([k,v])=>[k.replaceAll('_',' '),['state','proof_state','competition_state','submission_kind','match'].includes(k)&&typeof v==='string'?humanState(v):humanEvidence(v)])):value;
const verificationLabel=observation=>observation.submission_kind==='administrative'&&observation.proof_state==='claimed'&&!observation.proof_sources.length&&!observation.source_metadata_errors?.length&&!observation.proof_review?'Not a proof claim':observation.proof_state==='claimed'?'Claimed · not independently verified':observation.proof_state==='source_linked'?'Source linked · not independently verified':humanState(observation.proof_state);
const prCoverageComplete=data.competition_complete&&data.competition_acquisition?.scopes?.pull_requests===true;
const prStatusLabels={open:'Open',merged:'Merged','closed-unmerged':'Closed, unmerged',no_open:'No open PR'};
const matchesPRStatus=(row,value)=>value==='no_open'?prCoverageComplete&&!row.competition.some(i=>i.kind==='pull_request'&&i.state==='open'):row.competition.some(i=>i.kind==='pull_request'&&i.state===value);
const coverage=(acquisition,complete)=>complete?'complete':'incomplete';
byId('freshness').textContent='Saved snapshot · PR/Issues '+(data.competition_acquisition?.observed_at??'unknown')+' ('+coverage(data.competition_acquisition,data.competition_complete)+') · Awards '+(data.award_acquisition?.observed_at??'unknown')+' ('+coverage(data.award_acquisition,data.award_acquisition?.complete)+')';
byId('freshness').title='Vendor '+(data.scanner_provenance?.upstream_commit??'unknown')+' · Award revision '+(data.award_acquisition?.upstream_commit??'unknown');
const awardCounts=Object.fromEntries(Object.keys(awardLabels).map(state=>[state,data.rows.filter(r=>r.filters.award_state===state).length]));
const countStatus=(key,value)=>data.rows.filter(r=>r.filters[key]===value).length;
const metrics=[['Total problems',data.rows.length],['Math Open',countStatus('problem_status','Open')],['Lean No',countStatus('lean_status','No')],['Awards announced',awardCounts.announced]];
for(const [label,value] of metrics){const n=element('div',undefined,'card');n.append(element('b',value),element('span',label));byId('kpis').append(n);}
const columns=[['jsp_id','Problem'],['problem_status','Math status'],['lean_status','Lean'],['area','Area'],['prs','PRs'],['issues','Issues'],['award_state','Award']];
const countMatches=(row,key)=>row.competition.filter(i=>i.kind===(key==='prs'?'pull_request':'issue')).length;
const values=(r,key)=>key==='prs'||key==='issues'?[countMatches(r,key)]:[r.filters[key]??r[key]??'unknown'];
const filters=['problem_status','lean_status','area','award_state','prs','issues','pr_status'];
const filterLabels={problem_status:'Math status',lean_status:'Lean',area:'Area',award_state:'Award',prs:'PRs',issues:'Issues',pr_status:'PR status'};
const awardOrder={announced:0,candidate:1,none_in_scope:2,unknown:3};
for(const key of filters){const label=element('label',filterLabels[key]);const select=element('select');select.id='filter-'+key;select.append(new Option('All',''));const options=key==='pr_status'?Object.keys(prStatusLabels):key==='prs'||key==='issues'?[...Array.from({length:11},(_,i)=>String(i)),'>10']:key==='award_state'?['announced','candidate','none_in_scope']:[...new Set(data.rows.flatMap(r=>values(r,key)))].sort();for(const value of options){const option=new Option(key==='pr_status'?prStatusLabels[value]:key==='award_state'?awardLabels[value]:humanState(value),String(value));if(key==='pr_status'&&value==='no_open'&&!prCoverageComplete){option.disabled=true;option.title='Unavailable: complete version 2 PR coverage is required';}select.append(option);}if(key==='pr_status'&&!prCoverageComplete)select.title='No open PR is unavailable with incomplete evidence';select.addEventListener('change',()=>{page=1;render();});label.append(select);byId('filters').append(label);}
const awardText=row=>{if(row.filters.award_state!=='announced')return awardLabels[row.filters.award_state]??'Unknown';const announced=row.awards.filter(a=>a.state==='announced');const amounts=[...new Set(announced.filter(a=>a.published_amount!==null&&a.published_amount!==undefined&&(row.published_amounts??[]).some(p=>p.url===a.url&&p.currency===a.currency&&p.amount===a.published_amount)).map(a=>a.currency+' '+a.published_amount))];const missing=announced.some(a=>a.published_amount===null||a.published_amount===undefined);return 'Award announced · '+(amounts.length?amounts.join('; ')+(missing?'; Amount not published for other records':''):'Amount not published');};
let page=1,sortKey='jsp_id',descending=false;
for(const [key,label] of columns){const th=element('th');th.scope='col';const button=element('button',label);button.dataset.sort=key;button.addEventListener('click',()=>{descending=sortKey===key?!descending:false;sortKey=key;page=1;render();});th.append(button);byId('columns').append(th);}
function detail(row,kind=null){
 const body=byId('detail-body');body.replaceChildren(element('div','Problem inspection','eyebrow'),element('h2',row.jsp_id+' · '+row.title));
 byId('detail-body').querySelector('h2').id='detail-title';
 field(body,'Captured competition classification',humanState(row.competition_state));
 field(body,'Selection profiles and reasons',humanEvidence(row.profiles));
 const sections=[['Original mathematical problem and citations',row.official.fields||{}],['Official catalog status, eligibility and claims',row.official],['Mathematical solution evidence (reviewed)',row.solution],['Non-official research estimates and rationales',row.research],['Independent proof reviews',humanEvidence(row.proof_reviews)],['Official candidate / announced-award records (not payment)',humanEvidence(row.awards)],['Historical bounty (separate from awards)',row.historical_bounty],['Publication-backed amounts',row.published_amounts],['Score and ranking rationale',{components:row.score_components,score:row.score,rationale:row.ranking_reason}],['Uncertainty',row.uncertainty],['Catalog provenance',row.source]];
 for(const [label,value] of sections){const d=element('details');d.open=label.startsWith('Original mathematical')||label==='Uncertainty';d.append(element('summary',label));if(value&&typeof value==='object'&&!Array.isArray(value)){for(const [k,v] of Object.entries(value))field(d,k,v);}else d.append(element('pre',show(value)));body.append(d);}
 for(const recordKind of ['pull_request','issue']){const d=element('details');d.id='detail-'+recordKind;d.open=true;const summary=element('summary',recordKind==='issue'?'Captured Issues':'Captured PRs');d.append(summary);const matches=row.competition.filter(i=>i.kind===recordKind);if(!matches.length)d.append(element('p',data.competition_complete?'No matching observations in complete captured scope.':'No matching saved observations; insufficient coverage.'));for(const i of matches){const heading=element('h3');heading.append(row.links.includes(i.url)?link(i.url,'#'+i.number+' · '+i.title):element('span','#'+i.number+' · '+i.title));d.append(heading);field(d,'Observed state',humanState(i.state));field(d,'Submission classification',humanState(i.submission_kind));field(d,'Verification state',verificationLabel(i));d.append(element('pre',show({...humanEvidence(i),'proof state':verificationLabel(i)})));}body.append(d);}
 const links=element('details');links.open=true;links.append(element('summary','Validated source links · manual investigation'));for(const href of row.links){const p=element('p');p.append(link(href));links.append(p);}body.append(links);
 if(!byId('detail').open)byId('detail').showModal();
 if(kind){const section=byId('detail-'+kind);section.open=true;section.querySelector('summary').focus();section.scrollIntoView({block:'start'});}
}
function render(){
 const query=byId('search').value.trim().toLocaleLowerCase();
 const filtered=data.rows.filter(r=>(!query||JSON.stringify(r).toLocaleLowerCase().includes(query))&&filters.every(key=>{const value=byId('filter-'+key).value;return !value||(key==='pr_status'?matchesPRStatus(r,value):key==='prs'||key==='issues'?(value==='>10'?countMatches(r,key)>10:countMatches(r,key)===Number(value)):values(r,key).map(String).includes(value));}));
 const sortValue=r=>sortKey==='award_state'?awardOrder[r.filters.award_state]:sortKey==='prs'||sortKey==='issues'?countMatches(r,sortKey):values(r,sortKey).map(show).join(', ');
 filtered.sort((a,b)=>{const x=sortValue(a),y=sortValue(b);let order=sortKey==='prs'||sortKey==='issues'||sortKey==='award_state'?Number(x)-Number(y):x<y?-1:x>y?1:0;return (descending?-order:order)||(a.jsp_id<b.jsp_id?-1:a.jsp_id>b.jsp_id?1:0);});
 const size=Number(byId('page-size').value),pages=Math.max(1,Math.ceil(filtered.length/size));page=Math.min(page,pages);
 byId('rows').replaceChildren();
 for(const r of filtered.slice((page-1)*size,page*size)){const tr=element('tr');tr.dataset.jspId=r.jsp_id;for(const [key] of columns){const td=element('td');if(key==='jsp_id'){const button=element('button',r.jsp_id,'identity');button.addEventListener('click',()=>detail(r));td.append(button,element('span',r.title,'title'));if(r.catalog_url)td.append(link(r.catalog_url,'Official catalog'));}else if(key==='prs'||key==='issues'){const kind=key==='prs'?'pull_request':'issue',label=key==='prs'?'PRs':'Issues',count=countMatches(r,key);const control=element(count?'button':'span',String(count));if(count){control.dataset.kind=kind;control.setAttribute('aria-label',count+' '+label+' for '+r.jsp_id);control.addEventListener('click',()=>detail(r,kind));}td.append(control);}else if(key==='award_state')td.textContent=awardText(r);else td.textContent=values(r,key).map(humanState).join(', ');tr.append(td);}byId('rows').append(tr);}
 byId('results').textContent=filtered.length?filtered.length+' matching records of '+data.rows.length:'No matching records. Reset filters to inspect all candidates.';
 byId('page').textContent='Page '+page+' of '+pages;byId('previous').disabled=page<=1;byId('next').disabled=page>=pages;
 for(const th of byId('columns').children)th.setAttribute('aria-sort',th.firstChild.dataset.sort===sortKey?(descending?'descending':'ascending'):'none');
}
for(const id of ['search','page-size'])byId(id).addEventListener(id==='search'?'input':'change',()=>{page=1;render();});
byId('previous').addEventListener('click',()=>{page--;render();});byId('next').addEventListener('click',()=>{page++;render();});
byId('close').addEventListener('click',()=>byId('detail').close());
byId('reset').addEventListener('click',()=>{byId('search').value='';for(const key of filters)byId('filter-'+key).value='';page=1;render();});
render();
</script>
</body></html>
"""
