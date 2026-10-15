"""Exercise real offline numerical controls in Chromium, including small screens.

Install numerical/browser-requirements.txt and `playwright install chromium`.
This checks behavior against the saved solution arrays, not a mocked DOM.
"""
from pathlib import Path
import json
from playwright.sync_api import sync_playwright

ROOT=Path(__file__).resolve().parents[1]
DATA=json.loads((ROOT/"docs/numerical-data/solutions.json").read_text())
checks=0
def check(condition,message):
    global checks
    if not condition:raise AssertionError(message)
    checks+=1

with sync_playwright() as p:
    browser=p.chromium.launch()
    page=browser.new_page(viewport={"width":1440,"height":1100},device_scale_factor=1)
    errors=[];remote=[]
    page.on("pageerror",lambda e:errors.append(str(e)))
    page.on("request",lambda r:remote.append(r.url) if r.url.startswith(("http://","https://")) else None)
    page.goto((ROOT/"docs/numerical.html").as_uri())
    check(page.title()=="Matrix Transport · The Reaction-Zero Limit","page title")
    for scenario in ["finite","infinite"]:
        page.locator('#'+scenario).click()
        results=list(DATA[scenario]["solutions"])
        if scenario=="finite":results.append(DATA[scenario]["balanced"])
        for i,r in enumerate(results):
            page.locator(f'#weights button[data-index="{i}"]').click()
            actual=float(page.locator("#action").inner_text())
            check(abs(actual-r["primal_total"])<6e-6,"displayed action disagrees with solved data")
            check(page.locator(f'#weights button[data-index="{i}"]').get_attribute("aria-pressed")=="true","weight selection")
            for time in [0,.5,1]:
                page.locator("#time").evaluate("(e,value)=>{e.value=value;e.dispatchEvent(new Event('input',{bubbles:true}))}",round(time*1000))
                k=round(time*r["nt"])
                expected=r["dx"]*sum(m[0][0]+m[1][1] for m in r["rho"][k])
                check(abs(float(page.locator("#trace").inner_text())-expected)<6e-5,"displayed trace disagrees with matrix data")
        check(page.locator("#compare").is_disabled()==(scenario=="infinite"),"balanced overlay availability")
    page.locator("#finite").click();page.locator("#compare").check()
    page.locator("#play").click();page.wait_for_timeout(260)
    check(float(page.locator("#time").input_value())>0,"animation advances time")
    page.locator("#play").click()
    check(page.locator("#play").get_attribute("aria-pressed")=="false","animation pause")
    for width in [390,320,768]:
        page.set_viewport_size({"width":width,"height":844})
        page.locator("#technical").evaluate("e=>e.open=true")
        page.wait_for_timeout(170)
        check(not page.evaluate("document.documentElement.scrollWidth > innerWidth"),f"horizontal overflow at {width}px")
    with page.expect_download() as event:page.locator("#download").click()
    check(json.loads(Path(event.value.path()).read_text())==DATA,"downloaded dataset is the original data")
    with page.expect_download() as event:page.locator("#snapshot").click()
    check(Path(event.value.path()).read_bytes().startswith(b"\x89PNG\r\n\x1a\n"),"frame export is PNG")
    page.set_viewport_size({"width":1440,"height":1100})
    page.locator("#finite").click()
    page.locator('#weights button[data-index="1"]').click()
    page.locator("#time").evaluate("e=>{e.value=460;e.dispatchEvent(new Event('input',{bubbles:true}))}")
    page.locator("#technical").evaluate("e=>e.open=false")
    page.wait_for_timeout(170)
    check(not errors,f"browser errors: {errors}")
    check(not remote,f"unexpected external asset requests: {remote}")
    if (ROOT/".verification").is_dir():
        page.screenshot(path=str(ROOT/".verification/numerical-reviewed.png"),full_page=True)
    # The standalone CLI omits an MLflow run ID. Re-render the same arrays with
    # that metadata state and exercise real page initialization.
    original_payload=json.dumps(DATA,separators=(",",":"),allow_nan=False).replace("<","\\u003c")
    missing_data={**DATA,"metadata":{**DATA["metadata"],"mlflow_run_id":None}}
    missing_payload=json.dumps(missing_data,separators=(",",":"),allow_nan=False).replace("<","\\u003c")
    html=(ROOT/"docs/numerical.html").read_text()
    check(html.count(original_payload)==1,"embedded payload located")
    # set_content on the existing window would redeclare the global const DATA.
    # A fresh page models opening a separately generated standalone HTML file.
    page.close()
    page=browser.new_page(viewport={"width":1440,"height":1100},device_scale_factor=1)
    page.on("pageerror",lambda e:errors.append(str(e)))
    page.on("request",lambda r:remote.append(r.url) if r.url.startswith(("http://","https://")) else None)
    page.set_content(html.replace(original_payload,missing_payload))
    check(page.locator("#run-id").inner_text()=="Tracking not enabled","missing run ID label")
    page.locator("#infinite").click()
    check(float(page.locator("#action").inner_text())>0,"untracked page remains interactive")
    check(not errors,f"browser errors after missing run ID: {errors}")
    check(not remote,f"unexpected external asset requests after missing run ID: {remote}")
    browser.close()
print(f"PASS: {checks} browser checks (offline data, all weights, time, playback, overlay, exports, responsive layout).")
