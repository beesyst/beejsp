from __future__ import annotations

import json
import os
import select
import time
import shutil
import subprocess
import tempfile
from pathlib import Path

import test_dashboard as fixtures
import test_discovery as observations

from beejsp import dashboard
from beejsp.scanner import scan_problem_bank

CHECKS = r"""
<script>
try {
 const passed=[];
 const check=(name,condition)=>{if(!condition)throw Error(name);passed.push(name);};
 const event=(id,value)=>{byId(id).value=value;byId(id).dispatchEvent(new Event(id==='search'?'input':'change'));};
 const shown=()=>[...document.querySelectorAll('#rows tr')].map(tr=>tr.dataset.jspId);
 check('complete catalog',data.rows.length===1022&&new Set(data.rows.map(r=>r.jsp_id)).size===1022&&byId('results').textContent.startsWith('1022 matching'));
 check('seven overview columns',document.querySelectorAll('#columns th').length===7&&[...document.querySelectorAll('#columns button')].map(n=>n.textContent).join('|')==='Problem|Math status|Lean|Area|PRs|Issues|Award');
 check('seven filters without profiles',filters.join('|')==='problem_status|lean_status|area|award_state|prs|issues|pr_status'&&!byId('profile')&&!byId('membership')&&!byId('counts'));
 check('redundant notice removed',[...document.querySelectorAll('p')].every(n=>!n.textContent.includes('Saved snapshot, not live state'))&&!document.querySelector('p.notice'));
 const cards=[...document.querySelectorAll('#kpis .card')];
 check('four derived metrics',cards.length===4&&cards.every((n,i)=>n.querySelector('span').textContent===metrics[i][0]&&Number(n.querySelector('b').textContent)===metrics[i][1]));
 check('exact metric labels',metrics.map(m=>m[0]).join('|')==='Total problems|Math Open|Lean No|Awards announced');
 check('Lean Unknown stays separate',metrics[2][1]===data.rows.filter(r=>r.filters.lean_status==='No').length&&data.rows.some(r=>r.filters.lean_status==='Unknown')&&metrics[2][1]+data.rows.filter(r=>r.filters.lean_status==='Yes').length<data.rows.length);
 check('catalog status boundary',document.body.textContent.includes('Lean status is recorded by the official catalog'));
 check('award filter omits Unknown',[...byId('filter-award_state').options].map(o=>o.value).join('|')==='|announced|candidate|none_in_scope');
 const rgb=value=>value.match(/\d+/g).slice(0,3).map(Number);
 const luminance=color=>rgb(color).map(c=>{c/=255;return c<=.04045?c/12.92:((c+.055)/1.055)**2.4;}).reduce((a,c,i)=>a+c*[.2126,.7152,.0722][i],0);
 const contrast=n=>{const style=getComputedStyle(n),a=luminance(style.color),b=luminance(style.backgroundColor);return (Math.max(a,b)+.05)/(Math.min(a,b)+.05);};
 check('dark default',getComputedStyle(document.documentElement).colorScheme==='dark'&&luminance(getComputedStyle(document.body).backgroundColor)<.1);
 check('readable contrast',[document.body,...document.querySelectorAll('.card,input,select,dialog')].every(n=>contrast(n)>=4.5));
 check('dark surfaces',[...document.querySelectorAll('.card,input,select,dialog')].every(n=>luminance(getComputedStyle(n).backgroundColor)<.1));
 check('focus affordance',document.querySelector('style').textContent.includes(':focus-visible')&&document.querySelector('style').textContent.includes("th[aria-sort='ascending']"));
 check('compact freshness',byId('freshness').textContent.includes(data.competition_acquisition.observed_at)&&!byId('freshness').textContent.includes('repository'));
 check('first page',shown().length===25&&byId('page').textContent==='Page 1 of 41');
 byId('next').click();check('pagination next',shown()[0]===data.rows[25].jsp_id);
 byId('previous').click();check('pagination previous',shown()[0]===data.rows[0].jsp_id);
 event('page-size','100');check('page size',shown().length===100&&byId('page').textContent==='Page 1 of 11');
 const allSeen=[];do{allSeen.push(...shown());if(byId('next').disabled)break;byId('next').click();}while(true);
 check('all 1022 identities accessible',new Set(allSeen).size===1022);
 byId('reset').click();document.querySelector('[data-sort="jsp_id"]').click();check('descending stable sort',shown()[0]===data.rows.at(-1).jsp_id);document.querySelector('[data-sort="jsp_id"]').click();
 for(const key of filters){const option=byId('filter-'+key).options[1].value;event('filter-'+key,option);const expected=data.rows.filter(r=>key==='pr_status'?r.competition.some(i=>i.kind==='pull_request'&&i.state===option):values(r,key).map(String).includes(option));check('filter '+key,shown().every(id=>expected.some(r=>r.jsp_id===id))&&(expected.length?byId('results').textContent.startsWith(expected.length+' matching'):byId('results').textContent.startsWith('No matching')));byId('reset').click();}
 const observedCount=(r,key)=>r.competition.reduce((count,i)=>count+(i.kind===(key==='prs'?'pull_request':'issue')),0);
 const countOptions=['',...Array.from({length:11},(_,i)=>String(i)),'>10'];
 const matchesCount=(r,key,value)=>value===''|| (value==='>10'?observedCount(r,key)>=11:observedCount(r,key)===Number(value));
 for(const key of ['prs','issues']){check('exact options '+key,[...byId('filter-'+key).options].map(o=>o.value).join('|')===countOptions.join('|'));for(const option of countOptions){byId('reset').click();event('filter-'+key,option);const expected=data.rows.filter(r=>matchesCount(r,key,option));check(key+' count option '+(option||'All'),shown().every(id=>expected.some(r=>r.jsp_id===id))&&(expected.length?byId('results').textContent.startsWith(expected.length+' matching'):byId('results').textContent.startsWith('No matching'))&&byId('page').textContent.startsWith('Page 1 of'));}}
 for(const [prs,issues] of [['0','0'],['3',''],['>10','0']]){byId('reset').click();event('filter-prs',prs);event('filter-issues',issues);const expected=data.rows.filter(r=>matchesCount(r,'prs',prs)&&matchesCount(r,'issues',issues));check('combined counts '+prs+'/'+(issues||'All'),shown().every(id=>expected.some(r=>r.jsp_id===id))&&(expected.length?byId('results').textContent.startsWith(expected.length+' matching'):byId('results').textContent.startsWith('No matching')));}
 byId('reset').click();byId('next').click();event('filter-prs','10');check('filter resets pagination',byId('page').textContent.startsWith('Page 1 of'));
 event('search','no-such-problem-xyz');byId('reset').click();check('reset clears search and seven filters',byId('search').value===''&&filters.every(k=>byId('filter-'+k).value==='')&&byId('page').textContent.startsWith('Page 1 of'));
 const seed=data.rows.some(r=>r.title.includes('count-filter-fixture'));
 for(const key of ['prs','issues']){byId('reset').click();if(seed)event('search','count-filter-fixture');const candidates=data.rows.filter(r=>!seed||r.title.includes('count-filter-fixture'));for(const descending of [false,true]){document.querySelector('[data-sort="'+key+'"]').click();const expected=[...candidates].sort((a,b)=>(descending?-1:1)*(observedCount(a,key)-observedCount(b,key))||a.jsp_id.localeCompare(b.jsp_id));check('numeric '+key+' sort '+(descending?'descending':'ascending'),shown().join('|')===expected.slice(0,100).map(r=>r.jsp_id).join('|'));}if(seed){const equal=shown().filter(id=>observedCount(data.rows.find(r=>r.jsp_id===id),key)===(key==='prs'?2:10));check('stable JSP ties '+key,equal.join('|')===[...equal].sort().join('|'));}}
 byId('reset').click();document.querySelector('[data-sort="jsp_id"]').click();
 for(const key of ['prs','issues']){byId('reset').click();const other=key==='prs'?'issues':'prs';event('filter-'+other,'2');if(sortKey===key)document.querySelector('[data-sort="jsp_id"]').click();const candidates=data.rows.filter(r=>observedCount(r,other)===2);for(const descending of [false,true]){document.querySelector('[data-sort="'+key+'"]').click();const expected=[...candidates].sort((a,b)=>(descending?-1:1)*(observedCount(a,key)-observedCount(b,key))||a.jsp_id.localeCompare(b.jsp_id));check('numeric filtered '+key+' '+(descending?'descending':'ascending'),shown().join('|')===expected.slice(0,100).map(r=>r.jsp_id).join('|')&&byId('page').textContent.startsWith('Page 1 of'));}}
 byId('reset').click();document.querySelector('[data-sort="jsp_id"]').click();
 const sample=data.rows.find(r=>r.filters.award_state==='announced');
 event('search',sample.jsp_id);for(const key of filters.filter(k=>k!=='pr_status')){const value=key==='prs'||key==='issues'?(observedCount(sample,key)>10?'>10':String(observedCount(sample,key))):sample.filters[key];event('filter-'+key,value);}check('all numeric/catalog filters AND search',shown().includes(sample.jsp_id)&&shown().every(id=>{const r=data.rows.find(r=>r.jsp_id===id);return filters.filter(k=>k!=='pr_status').every(k=>k==='prs'||k==='issues'?matchesCount(r,k,byId('filter-'+k).value):r.filters[k]===byId('filter-'+k).value);}));
 byId('reset').click();
 const lifecycleOptions=[['','All'],['open','Open'],['merged','Merged'],['closed-unmerged','Closed, unmerged'],['no_open','No open PR']];
 check('exact PR status options',[...byId('filter-pr_status').options].map(o=>o.value+'='+o.textContent).join('|')===lifecycleOptions.map(([v,l])=>v+'='+l).join('|'));
 check('negative lifecycle guarded',byId('filter-pr_status').options[4].disabled===!data.competition_complete);
 for(const [state] of lifecycleOptions){byId('reset').click();event('filter-pr_status',state);const expected=data.rows.filter(r=>!state||(state==='no_open'?data.competition_complete&&!r.competition.some(i=>i.kind==='pull_request'&&i.state==='open'):r.competition.some(i=>i.kind==='pull_request'&&i.state===state)));check('PR lifecycle '+(state||'All'),shown().every(id=>expected.some(r=>r.jsp_id===id))&&(expected.length?byId('results').textContent.startsWith(expected.length+' matching'):byId('results').textContent.startsWith('No matching'))&&byId('page').textContent.startsWith('Page 1 of'));}
 byId('reset').click();event('filter-problem_status','Solved');event('filter-lean_status','No');event('filter-pr_status','open');event('filter-prs','3');event('filter-issues','1');const combined=data.rows.filter(r=>r.filters.problem_status==='Solved'&&r.filters.lean_status==='No'&&observedCount(r,'prs')===3&&observedCount(r,'issues')===1&&r.competition.some(i=>i.kind==='pull_request'&&i.state==='open'));check('lifecycle AND solved Lean No numeric filters',shown().every(id=>combined.some(r=>r.jsp_id===id))&&(combined.length?byId('results').textContent.startsWith(combined.length+' matching'):byId('results').textContent.startsWith('No matching')));
 byId('reset').click();event('filter-pr_status','merged');event('search','JSP-000161');check('lifecycle with text search',shown().every(id=>JSON.stringify(data.rows.find(r=>r.jsp_id===id)).toLowerCase().includes('jsp-000161')));byId('reset').click();check('reset clears lifecycle',byId('filter-pr_status').value==='');
 for(const [state,label] of Object.entries(awardLabels).filter(([state])=>state!=='unknown')){event('filter-award_state',state);const expected=data.rows.filter(r=>r.filters.award_state===state);check('award count '+state,expected.length?byId('results').textContent.startsWith(expected.length+' matching'):shown().length===0&&byId('results').textContent.startsWith('No matching'));check('award label '+state,byId('filter-award_state').selectedOptions[0].textContent===label);}
 byId('reset').click();document.querySelector('[data-sort="award_state"]').click();check('announced awards sorted first',shown()[0]===data.rows.filter(r=>r.filters.award_state==='announced').sort((a,b)=>a.jsp_id.localeCompare(b.jsp_id))[0].jsp_id);
 document.querySelector('[data-sort="jsp_id"]').click();
 event('search','JSP-000161');check('local search',shown().includes('JSP-000161'));
 const target=[...document.querySelectorAll('#rows tr')].find(r=>r.dataset.jspId==='JSP-000161');target.querySelector('button').click();
 check('accessible detail title',byId('detail').getAttribute('aria-labelledby')==='detail-title'&&byId('detail-title').textContent.includes('JSP-000161'));
 byId('close').click();
 for(const kind of ['pull_request','issue']){const record=data.rows.find(r=>r.jsp_id==='JSP-000161'&&r.competition.some(i=>i.kind===kind))??data.rows.find(r=>r.competition.some(i=>i.kind===kind));event('search',record.jsp_id);const tr=[...byId('rows').children].find(n=>n.dataset.jspId===record.jsp_id);const activity=tr.querySelector('[data-kind="'+kind+'"]');check('interactive '+kind+' count',activity&&activity.tagName==='BUTTON'&&activity.getAttribute('aria-label').includes(record.jsp_id));activity.focus();check('keyboard focus '+kind,document.activeElement===activity);activity.click();check('focused '+kind+' list',byId('detail').open&&document.activeElement===byId('detail-'+kind).querySelector('summary'));const expected=record.competition.filter(i=>i.kind===kind);check('canonical '+kind+' links',expected.every(i=>[...byId('detail-'+kind).querySelectorAll('h3 a')].some(a=>a.href===i.url)));check('record classifications '+kind,byId('detail-'+kind).textContent.includes('Observed state')&&byId('detail-'+kind).textContent.includes('Submission classification')&&byId('detail-'+kind).textContent.includes('Verification state'));byId('close').click();}
 event('search','JSP-000161');[...byId('rows').children].find(n=>n.dataset.jspId==='JSP-000161').querySelector('button').click();
 check('details and both profiles',byId('detail').open&&byId('detail-body').textContent.includes('Selection profiles and reasons')&&byId('detail-body').textContent.includes('high-value'));
 check('explicit unverified label',verificationLabel({submission_kind:'lean',proof_state:'claimed',proof_sources:[],proof_review:null})==='Claimed · not independently verified');
 check('explicit source label',verificationLabel({submission_kind:'lean',proof_state:'source_linked',proof_sources:[{}]})==='Source linked · not independently verified');
 check('administrative is not a proof claim',verificationLabel({submission_kind:'administrative',proof_state:'claimed',proof_sources:[],proof_review:null})==='Not a proof claim');
 check('independent review label retained',verificationLabel({submission_kind:'lean',proof_state:'independently_verified',proof_sources:[{}],proof_review:{state:'independently_verified'}})==='Independently verified');
 check('invalid administrative claim not hidden',verificationLabel({submission_kind:'administrative',proof_state:'unresolved',proof_sources:[],source_metadata_errors:['invalid source']})==='Unresolved');
 check('human proof labels',Object.entries(proofLabels).every(([state,label])=>humanState(state)===label)&&!byId('detail-body').textContent.includes('"proof_state"'));
 const links=[...byId('detail-body').querySelectorAll('a')];check('safe manual links',links.length>0&&links.every(a=>a.protocol==='https:'&&a.target==='_blank'&&a.rel==='noopener noreferrer'&&!a.username));
 check('canonical official links',links.some(a=>a.href.includes('/TheJustinSunPrize/awards/')));
 if(data.rows.some(r=>r.title.includes('unique-hostile-title'))){check('hostile markup inert',!globalThis.injected&&!document.querySelector('img')&&byId('detail-body').textContent.includes('<img'));check('invalid metadata preserved',byId('detail-body').textContent.includes('proof commit must be a full SHA')&&byId('detail-body').textContent.includes('Unresolved'));check('genuine Lean claim detail',byId('detail-issue').textContent.includes('Claimed · not independently verified'));check('linked source detail',byId('detail-pull_request').textContent.includes('Source linked · not independently verified'));check('mixed lifecycle and administrative detail',byId('detail-pull_request').textContent.includes('Open')&&byId('detail-pull_request').textContent.includes('Merged')&&byId('detail-pull_request').textContent.includes('Closed, unmerged')&&byId('detail-pull_request').textContent.includes('Not a proof claim'));check('review labels and pins',byId('detail-body').textContent.includes('Independently verified')&&links.some(a=>a.href.includes('/blob/'+ 'a'.repeat(40)+'/Main.lean')));}
 byId('close').click();check('close details',!byId('detail').open);
 if(seed){event('search','JSP-000475');[...byId('rows').children].find(n=>n.dataset.jspId==='JSP-000475').querySelector('button').click();check('verified observation remains verified',byId('detail-pull_request').textContent.includes('Independently verified')&&!byId('detail-pull_request').textContent.includes('not independently verified'));byId('close').click();}
 event('search','no-such-problem-xyz');check('empty results',shown().length===0&&byId('results').textContent.startsWith('No matching'));
 byId('reset').click();event('filter-award_state','announced');document.querySelector('#rows button').click();
 check('official record details',byId('detail-body').textContent.includes('Award announced')&&byId('detail-body').textContent.includes('not payment')&&[...byId('detail-body').querySelectorAll('a')].some(a=>a.href.includes('/awards/README.md')));byId('close').click();
 byId('reset').click();document.querySelector('[data-sort="jsp_id"]').click();document.querySelector('[data-sort="jsp_id"]').click();
 const zeroRow=data.rows.find(r=>r.competition.length===0);
 if(zeroRow){event('search',zeroRow.jsp_id);const tr=[...byId('rows').children].find(n=>n.dataset.jspId===zeroRow.jsp_id);check('noninteractive zero counts',tr.children[4].textContent==='0'&&tr.children[5].textContent==='0'&&!tr.children[4].querySelector('button')&&!tr.children[5].querySelector('button'));}
 const unknownRow=data.rows.find(r=>r.filters.award_state==='unknown');
 if(zeroRow&&!data.competition_complete){check('zero counts preserve unknown coverage',zeroRow.competition_state==='UNKNOWN');byId('reset').click();event('search',zeroRow.jsp_id);[...byId('rows').children].find(n=>n.dataset.jspId===zeroRow.jsp_id).querySelector('button').click();check('zero detail keeps insufficient evidence',byId('detail-body').textContent.includes('insufficient coverage'));byId('close').click();}
 if(unknownRow){byId('reset').click();event('search',unknownRow.jsp_id);const tr=[...byId('rows').children].find(n=>n.dataset.jspId===unknownRow.jsp_id);check('unknown award retained in All',byId('filter-award_state').value===''&&tr.children[6].textContent==='Unknown');}
 byId('reset').click();event('filter-award_state','announced');
 check('official amount cells',[...byId('rows').children].every(tr=>tr.children[6].textContent===awardText(data.rows.find(r=>r.jsp_id===tr.dataset.jspId))));
 if(data.rows.some(r=>r.title.includes('unique-hostile-title'))){const row=data.rows.find(r=>r.jsp_id==='JSP-000475');check('multiple published amounts',awardText(row).includes('USD 1234.50')&&awardText(row).includes('EUR 250')&&!awardText(row).includes('JPY')&&awardText(row).includes('Amount not published for other records'));check('unpublished announcement',awardText(data.rows.find(r=>r.jsp_id==='JSP-000161'))==='Award announced · Amount not published');check('candidate amount excluded',awardText(data.rows.find(r=>r.jsp_id==='JSP-000089'))==='Candidate registered');}
 else{check('saved announced amounts unpublished',data.rows.filter(r=>r.filters.award_state==='announced').every(r=>awardText(r)==='Award announced · Amount not published'));check('saved metrics reference',metrics.map(m=>m[1]).join('|')==='1022|649|940|6');}
 byId('reset').click();
 check('offline resources',performance.getEntriesByType('resource').length===0&&!document.querySelector('script[src]'));
 check('viewport layout',document.documentElement.scrollWidth<=innerWidth);
 const result=document.createElement('pre');result.id='browser-check-result';result.textContent=JSON.stringify({passed});document.body.append(result);
} catch(error) {const result=document.createElement('pre');result.id='browser-check-result';result.textContent=JSON.stringify({failed:String(error),width:innerWidth,documentWidth:document.documentElement.scrollWidth,overflow:[...document.querySelectorAll("body *")].filter(n=>n.getBoundingClientRect().right>innerWidth&&n.closest(".table-wrap")===null).slice(0,10).map(n=>({tag:n.tagName,id:n.id,right:n.getBoundingClientRect().right}))});document.body.append(result);}
</script>
"""


def main() -> int:
    browser = shutil.which("google-chrome") or shutil.which("chromium")
    if browser is None:
        raise SystemExit(
            "Installed Chrome or Chromium is required for this optional check"
        )
    saved = fixtures.inputs()
    saved["scanner"] = scan_problem_bank(fixtures.ROOT / "docs/vendor/jsp")
    record = next(r for r in saved["scanner"]["records"] if r["jsp_id"] == "JSP-000161")
    record["title"] = (
        "unique-hostile-title </script><script>globalThis.injected=true</script>"
    )
    record["official"]["fields"]["Problem description"] = (
        'Hostile problem <img src=x onerror="globalThis.injected=true"> [citation](https://example.org/paper) [bad](javascript:alert)'
    )
    record["official"]["fields"]["Attribution basis"] = (
        "Recorded Author (official fixture attribution)"
    )
    saved["competition"]["observations"] = fixtures.lifecycle_observations()
    saved["competition"]["observations"]["pull_requests"][0].update(
        proof_sources=[observations.source()],
        source_metadata_errors=["proof commit must be a full SHA"],
    )
    counts = fixtures.count_filter_observations()
    for category, records in counts.items():
        saved["competition"]["observations"][category].extend(records)
    saved["competition"]["acquisition"].update(
        complete=False, scopes={"pull_requests": False, "issues": False}
    )
    for index in range(13):
        item = next(
            r
            for r in saved["scanner"]["records"]
            if r["jsp_id"] == f"JSP-{index + 1:06d}"
        )
        item["title"] = f"count-filter-fixture {index}"
    saved["research"] = observations.research(
        observations.verified_review(),
        scientific_significance=observations.evidence(value="low"),
    )
    saved["research"]["candidates"].append(
        {
            "jsp_id": "JSP-000475",
            "proof_reviews": [
                {
                    **observations.verified_review(),
                    "subject_url": f"{observations.ROOT}/pull/1269",
                }
            ],
        }
    )
    saved["awards"]["records"] = fixtures.award_amount_records()
    saved["awards"]["acquisition"]["complete"] = False
    html = dashboard.build_reports(saved)["dashboard.html"].replace(
        "</body>", CHECKS + "</body>"
    )
    cases = [("hostile fixture", html)]
    if (fixtures.ROOT / "storage/discovery/current.json").exists():
        _, live = dashboard.load_snapshot(fixtures.ROOT)
        cases.append(
            (
                "saved live snapshot",
                dashboard.build_reports(live)["dashboard.html"].replace(
                    "</body>", CHECKS + "</body>"
                ),
            )
        )
    for label, html in cases:
        for width in (650, 1280):
            if run_browser(browser, f"{label} / {width}px", html, width):
                return 1
        check_keyboard(browser, label, html)
    return 0


def run_browser(browser: str, label: str, html: str, width: int) -> int:
    with tempfile.TemporaryDirectory(prefix="beejsp-browser-") as temporary:
        directory = Path(temporary)
        path = directory / "dashboard.html"
        path.write_text(html, encoding="utf-8")
        result = subprocess.run(
            [
                browser,
                "--headless",
                "--disable-gpu",
                "--disable-background-networking",
                "--no-first-run",
                "--no-default-browser-check",
                f"--window-size={width},850",
                f"--user-data-dir={directory / 'profile'}",
                "--dump-dom",
                path.as_uri(),
            ],
            capture_output=True,
            text=True,
            timeout=60,
            check=False,
        )
        if result.returncode:
            raise SystemExit(
                f"Chrome exited {result.returncode}: {result.stderr[-2000:]}"
            )
        import re
        from html import unescape

        match = re.search(
            r'<pre id="browser-check-result">(.*?)</pre>', result.stdout, re.S
        )
        if match is None:
            raise SystemExit("Browser checks did not execute")
        report = json.loads(unescape(match[1]))
        print(json.dumps({"case": label, **report}, indent=2))
        return 1 if "failed" in report else 0


def check_keyboard(browser: str, label: str, html: str) -> None:
    with tempfile.TemporaryDirectory(prefix="beejsp-keys-") as temporary:
        directory = Path(temporary)
        path = directory / "dashboard.html"
        path.write_text(html)
        command_read, command_write = os.pipe()
        event_read, event_write = os.pipe()
        process = subprocess.Popen(
            [
                "bash",
                "-c",
                'exec 3<&"$1" 4>&"$2"; shift 2; exec "$@"',
                "browser-pipe",
                str(command_read),
                str(event_write),
                browser,
                "--headless",
                "--disable-gpu",
                "--disable-background-networking",
                "--no-first-run",
                "--no-default-browser-check",
                "--remote-debugging-pipe",
                f"--user-data-dir={directory / 'profile'}",
            ],
            pass_fds=(command_read, event_write),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        os.close(command_read)
        os.close(event_write)
        buffer = b""
        request_id = 0
        session = None

        def request(method, params):
            nonlocal buffer, request_id
            request_id += 1
            packet = {"id": request_id, "method": method, "params": params}
            if session is not None:
                packet["sessionId"] = session
            os.write(command_write, json.dumps(packet).encode() + b"\0")
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline:
                if b"\0" not in buffer:
                    ready, _, _ = select.select([event_read], [], [], 1)
                    if not ready:
                        continue
                    chunk = os.read(event_read, 1_000_000)
                    if not chunk:
                        raise AssertionError("Chrome keyboard pipe closed")
                    buffer += chunk
                    continue
                message, buffer = buffer.split(b"\0", 1)
                response = json.loads(message)
                if response.get("id") == request_id:
                    assert "error" not in response, response
                    return response.get("result", {})
            raise AssertionError("Chrome keyboard check timed out")

        def evaluate(expression):
            result = request(
                "Runtime.evaluate", {"expression": expression, "returnByValue": True}
            )
            assert "exceptionDetails" not in result, result
            return result["result"].get("value")

        try:
            target = request("Target.createTarget", {"url": path.as_uri()})["targetId"]
            session = request(
                "Target.attachToTarget", {"targetId": target, "flatten": True}
            )["sessionId"]
            for _ in range(100):
                if evaluate("document.getElementById('rows')?.children.length > 0"):
                    break
                time.sleep(0.1)
            else:
                raise AssertionError("Dashboard did not load for keyboard check")
            passed = []
            for kind, key, code, number in [
                ("pull_request", "Enter", "Enter", 13),
                ("issue", " ", "Space", 32),
            ]:
                assert evaluate(
                    "(()=>{const r=data.rows.find(r=>r.competition.some(i=>i.kind==='"
                    + kind
                    + "'));byId('search').value=r.jsp_id;byId('search').dispatchEvent(new Event('input'));const tr=[...byId('rows').children].find(n=>n.dataset.jspId===r.jsp_id);tr.querySelector('[data-kind=\""
                    + kind
                    + "\"]').focus();return document.activeElement.dataset.kind==='"
                    + kind
                    + "';})()"
                )
                passed.append(kind + " native focus")
                for event in ("keyDown", "keyUp"):
                    request(
                        "Input.dispatchKeyEvent",
                        {
                            "type": event,
                            "key": key,
                            "code": code,
                            "windowsVirtualKeyCode": number,
                            "text": ("\r" if number == 13 else " ")
                            if event == "keyDown"
                            else "",
                        },
                    )
                assert evaluate(
                    "byId('detail').open&&document.activeElement===byId('detail-"
                    + kind
                    + "').querySelector('summary')"
                )
                passed.append(kind + " keyboard activation")
                for event in ("rawKeyDown", "keyUp"):
                    request(
                        "Input.dispatchKeyEvent",
                        {
                            "type": event,
                            "key": "Tab",
                            "code": "Tab",
                            "windowsVirtualKeyCode": 9,
                        },
                    )
                assert evaluate("byId('detail').contains(document.activeElement)")
                passed.append(kind + " modal Tab navigation")
                for event in ("rawKeyDown", "keyUp"):
                    request(
                        "Input.dispatchKeyEvent",
                        {
                            "type": event,
                            "key": "Escape",
                            "code": "Escape",
                            "windowsVirtualKeyCode": 27,
                        },
                    )
                assert evaluate("!byId('detail').open")
                passed.append(kind + " Escape closes dialog")
            print(
                json.dumps(
                    {"case": label + " / native keyboard", "passed": passed}, indent=2
                )
            )
        finally:
            session = None
            try:
                request("Browser.close", {})
            except (AssertionError, OSError):
                process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            os.close(command_write)
            os.close(event_read)


if __name__ == "__main__":
    raise SystemExit(main())
