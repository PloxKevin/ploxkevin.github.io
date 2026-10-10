const fs = require('fs'), vm = require('vm'), crypto = require('crypto');
const path='/home/oxrexkevin/SafetyBased/SafeLearning/primer-basics.html';
const html=fs.readFileSync(path,'utf8');
const marker='    // EXPLORER: fixed-point iteration (cobweb, error vs Banach bound) and the discounted geometric series';
const start=html.indexOf('    (function () {',html.indexOf(marker));
const end=html.indexOf('    })();',start)+'    })();'.length;
if(start<0 || end<start) throw Error('unique IIFE missing');
const body=html.slice(start,end); fs.writeFileSync('/tmp/modules-geometric858-explorer-exact-iife19-v2.js',body);
const elements={}; const defaults={'p0-map':'affine','p0-par':'0.5','p0-x0':'0','p0-n':'20','p0-g':'0.9','p0-T':'10'};
const get=(id)=>elements[id]||(elements[id]={value:defaults[id]||'',innerHTML:'',textContent:'',handlers:{},addEventListener(k,f){this.handlers[k]=f;}});
vm.runInNewContext(body,{document:{getElementById:get},Math,isFinite},{timeout:10000});
const results=[];
for(let cell=0;cell<=199;cell++) for(const T of [1,10,44,300]) {
 const gamma=cell/200; get('p0-g').value=String(gamma); get('p0-T').value=String(T);
 get('p0-g').handlers.input();
 const text=get('p0-ginfo').innerHTML;
 const captured=text.match(/99% needs T ≥ <b>(\d+)<\/b>; the rule T ≥ ln\(100\)\/\(1 − γ\) gives (\d+)\./);
 if(!captured || !get('p0-geo').innerHTML.includes('<polyline')) throw Error('panel render failed');
 const actualExact=+captured[1], actualCoarse=+captured[2];
 const independentlyCounted=gamma===0 ? 1 : (()=>{let n=0,num=1n,den=1n;while(100n*num>den){num*=BigInt(cell);den*=200n;n++;if(n>100000)throw Error('nontermination');}return n;})();
 const independentlyCoarse=Math.ceil(Math.log(100)/(1-gamma));
 if(actualExact!==independentlyCounted || actualCoarse!==independentlyCoarse) throw Error('counts mismatch');
 results.push({gamma,T,exact_count:actualExact,coarse_count:actualCoarse,rendered_panel:text});
}
const report={source:path,source_sha256:crypto.createHash('sha256').update(html).digest('hex'),exact_iife_sha256:crypto.createHash('sha256').update(body).digest('hex'),cases:results.length,allowed_gamma_slider_points:200,allowed_gamma_domain:'0 to 0.995 in increments of 0.005',tested_horizons:[1,10,44,300],all_counts_match_independent_exact_rational_power_count:true,results,limits:['Actual original IIFE run in Node with a minimal document; no browser or viewport observation.','Four horizons at every allowed slider gamma were executed; source drawGeo formula is independently read for all supported horizon integers.','JavaScript floats and display roundings are observations; the separate Lean proofs establish the real arithmetic.']};
fs.writeFileSync('/tmp/modules-geometric858-explorer-result19-v2.json',JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({cases:report.cases,all_counts_match:true,result:'/tmp/modules-geometric858-explorer-result19-v2.json'}));
