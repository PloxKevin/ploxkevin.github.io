    (function(){
      var $=function(id){return document.getElementById(id);};
      if(!$('ls-ce-svg1')) return;
      function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;var t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
      function gauss(r){var u=0,v=0;while(u===0)u=r();v=r();return Math.sqrt(-2*Math.log(u))*Math.cos(2*Math.PI*v);}
      // upper Gaussian tail Q(z)=P(N(0,1)>z)=erfc(z/sqrt2)/2, evaluated directly (Numerical Recipes erfcc, relative error below 1.2e-7 for every z);
      // computing it as 1-Phi(z) loses its relative accuracy in the tail and cancels to exactly 0 once Phi(z) rounds to 1 (z above about 8.3), which turned tiny expectations into false zeros
      function Q(z){var x=Math.abs(z)/Math.SQRT2,t=1/(1+0.5*x);
        var r=t*Math.exp(-x*x-1.26551223+t*(1.00002368+t*(0.37409196+t*(0.09678418+t*(-0.18628806+t*(0.27886807+t*(-1.13520398+t*(1.48851587+t*(-0.82215223+t*0.17087277)))))))));
        return z>=0?0.5*r:1-0.5*r;}
      var N=200, XG=0.8, XB=1.0, seedNo=1, TMAX=parseInt($('ls-ce-T').max,10)||100, Wn=null, Wseed=-1;
      // common random numbers: one N x TMAX matrix of standard normals per seed, reused by every slider setting
      function noise(){if(Wseed!==seedNo){var r=mulberry32(20260929+seedNo*7919);Wn=[];
          for(var i=0;i<N;i++){var row=[];for(var t=0;t<TMAX;t++)row.push(gauss(r));Wn.push(row);} Wseed=seedNo;} return Wn;}
      function simulate(k,sig,T){
        var W=noise(), trajs=[],Ns=[],Zs=[];
        for(var i=0;i<N;i++){var x=0,tr=[0],n=0,z=-XB,w=W[i];
          for(var t=0;t<T;t++){x=x-k*(x-XG)+sig*w[t];tr.push(x);if(x>XB)n++;if(x-XB>z)z=x-XB;}
          trajs.push(tr);Ns.push(n);Zs.push(z);}
        return {trajs:trajs,Ns:Ns,Zs:Zs};
      }
      // CVaR of the empirical distribution (atoms of mass 1/N): Rockafellar-Uryasev value with the split atom
      function cvar(Z,a){var s=Z.slice().sort(function(p,q){return q-p;});var kk=(1-a)*s.length,kf=Math.floor(kk),sum=0;
        for(var i=0;i<kf;i++)sum+=s[i]; if(kf<s.length)sum+=(kk-kf)*s[kf]; return sum/kk;}
      // lower alpha-quantile of the empirical law: the ceil(alpha*N)-th smallest value (1e-9 guards against 0.55*200=110.00000000000001)
      function varA(Z,a){var s=Z.slice().sort(function(p,q){return p-q;});var j=Math.ceil(a*s.length-1e-9)-1;return s[Math.max(0,Math.min(s.length-1,j))];}
      function exactEN(k,sig,T){var tot=0,den=1-(1-k)*(1-k);
        for(var t=1;t<=T;t++){var m=XG*(1-Math.pow(1-k,t)),v=Math.abs(den)<1e-12?sig*sig*t:sig*sig*(1-Math.pow(1-k,2*t))/den;
          tot+= v>0?Q((XB-m)/Math.sqrt(v)):(m>XB?1:0);} return tot;}
      function f(v,d){return v.toFixed(d);}
      // values known to be positive (pos) but below the displayed precision are shown in exponential form, so a rounded 0.000 is never read as an exact zero
      function fp(v,d,pos){if(!pos||v>=0.5*Math.pow(10,-d))return f(v,d);return v>0?v.toExponential(2):'positive, below the double-precision range';}
      function badge(ok,sample){return '<span style="display:inline-block;padding:1px 8px;border-radius:10px;font-size:11px;font-weight:700;color:#fff;background:'+(ok?'#2e7d32':'#c62828')+';">'+(sample?(ok?'SAMPLE PASSES':'SAMPLE FAILS'):(ok?'PASSES':'FAILS'))+'</span>';}
      function draw(){
        var k=parseFloat($('ls-ce-k').value),sig=parseFloat($('ls-ce-sig').value),T=parseInt($('ls-ce-T').value,10),a=parseFloat($('ls-ce-alpha').value),d=parseFloat($('ls-ce-d').value),del=parseFloat($('ls-ce-delta').value);
        $('ls-ce-k-val').textContent=f(k,2);$('ls-ce-sig-val').textContent=f(sig,2);$('ls-ce-T-val').textContent=T;$('ls-ce-alpha-val').textContent=f(a,2);$('ls-ce-d-val').textContent=f(d,1);$('ls-ce-delta-val').textContent=f(del,2);$('ls-ce-seed').textContent=seedNo;
        var S=simulate(k,sig,T), Ns=S.Ns, Zs=S.Zs;
        var Jc=0,nv=0,zmax=-1e9,zmean=0,ss=0,i,t;
        for(i=0;i<N;i++){Jc+=Ns[i];if(Ns[i]>0)nv++;if(Zs[i]>zmax)zmax=Zs[i];zmean+=Zs[i];}
        Jc/=N;zmean/=N;for(i=0;i<N;i++)ss+=(Ns[i]-Jc)*(Ns[i]-Jc);var seJ=Math.sqrt(ss/(N-1)/N);
        var pv=nv/N, sePv=Math.sqrt(pv*(1-pv)/N);
        var cv=cvar(Zs,a), va=varA(Zs,a), EN=exactEN(k,sig,T);
        var sInf=(k>0&&k<2)?sig/Math.sqrt(k*(2-k)):NaN, pInf=isNaN(sInf)?NaN:(sig>0?Q((XB-XG)/sInf):0);
        // the CMDP constraint concerns the true expectation, which is available exactly; the other verdicts are sample estimates.
        // With sigma>0 every marginal N(m_t,v_t) puts positive mass above 1, so E[N]>0 exactly and a zero budget fails even if the sum underflows.
        var zeroBudgetFails=sig>0&&d<=0;
        var okC=zeroBudgetFails?false:EN<=d, okP=pv<=del, okR=cv<=0, okH=zmax<=0;
        $('ls-ce-panel').innerHTML=
          '<div style="display:flex;flex-wrap:wrap;gap:6px 28px;">'+
          '<div><b>CMDP view</b> (cost = violating steps): analytical E[N] &asymp; <b>'+fp(EN,3,sig>0)+'</b> &nbsp;|&nbsp; sample mean '+f(Jc,3)+' &plusmn; '+f(seJ,3)+' &nbsp;|&nbsp; budget d = '+f(d,1)+' &nbsp;'+badge(okC)+' <span style="color:#888;">'+(zeroBudgetFails?'(d = 0 demands N = 0 almost surely; with &sigma; &gt; 0 every step violates with positive probability, so E[N] &gt; 0 and the budget fails)':'(analytical formula, evaluated numerically)')+'</span></div>'+
          '<div><b>Chance view</b>: P(any violation in the episode) &asymp; <b>'+f(pv,3)+'</b> &plusmn; '+f(sePv,3)+' (estimate) &nbsp;|&nbsp; level &delta; = '+f(del,2)+' &nbsp;'+badge(okP,true)+'</div>'+
          '<div><b>Risk view</b>: VaR<sub>&alpha;</sub>(Z) = '+f(va,3)+', <b>CVaR<sub>&alpha;</sub>(Z) = '+f(cv,3)+'</b> (mean of the worst '+Math.round((1-a)*100)+'% of the 200 sampled excursions; must be &le; 0) &nbsp;'+badge(okR,true)+'</div>'+
          '<div><b>Hard view</b>: worst sampled excursion max Z = <b>'+f(zmax,3)+'</b> (must be &le; 0 in every episode) &nbsp;'+badge(okH,true)+
          (sig>0?' <span style="color:#888;">&mdash; with Gaussian noise the true probability of ever violating is positive, so "almost surely safe" can never hold; 200 clean samples are not a proof.</span>':' <span style="color:#888;">&mdash; with &sigma; = 0 this checks exactly the trajectory from x = 0 through the selected horizon, not invariance of the whole safe set.</span>')+'</div>'+
          '<div style="color:#555;">Analytic: stationary sd &sigma;<sub>&infin;</sub> = &sigma;/&radic;(k(2&minus;k)) = '+(isNaN(sInf)?'n/a':f(sInf,4))+', stationary per-step violation probability p<sub>&infin;</sub> = 1 &minus; &Phi;((1 &minus; 0.8)/&sigma;<sub>&infin;</sub>) = '+(isNaN(pInf)?'n/a':fp(pInf,4,sig>0))+'; Markov bound on the chance view: P &le; E[N] = '+fp(EN,3,sig>0)+(EN>=1?' (vacuous)':'')+'.</div>'+
          '</div>';
        globalThis.__ceTrace = {k:k,sigma:sig,T:T,alpha:a,budget:d,delta:del,
          seedNo:seedNo,prngSeed:20260929+seedNo*7919,N:N,TMAX:TMAX,
          analyticEN:EN,stationarySD:sInf,stationaryTail:pInf,sampleMeanCount:Jc,
          sampleMeanSE:seJ,violatingEpisodes:nv,jointEstimate:pv,jointSE:sePv,
          sampleCVaR:cv,sampleVaR:va,maxExcursion:zmax,meanExcursion:zmean,
          zeroBudgetFails:zeroBudgetFails,cmdpPass:okC,chanceSamplePass:okP,
          riskSamplePass:okR,hardSamplePass:okH,Ns:Ns,Zs:Zs,trajs:S.trajs};
        // ---- plot 1: trajectories
        var W=700,H=260,ML=44,MR=14,MT=14,MB=32,PW=W-ML-MR,PH=H-MT-MB, xmin=1e9,xmax=-1e9;
        for(i=0;i<N;i++){var tr=S.trajs[i];for(t=0;t<tr.length;t++){if(tr[t]<xmin)xmin=tr[t];if(tr[t]>xmax)xmax=tr[t];}}
        var ylo=Math.min(-0.2,xmin-0.05), yhi=Math.max(1.4,xmax+0.05);
        function sx(tt){return ML+tt/T*PW;} function sy(x){return MT+PH*(1-(x-ylo)/(yhi-ylo));}
        var h='<rect x="'+ML+'" y="'+MT+'" width="'+PW+'" height="'+(sy(XB)-MT)+'" fill="#c62828" fill-opacity="0.06"/>';
        var step=(yhi-ylo)>3?1:(yhi-ylo)>1.5?0.5:0.2, g;
        for(g=Math.ceil(ylo/step)*step;g<=yhi+1e-9;g+=step){var yg=sy(g);h+='<line x1="'+ML+'" y1="'+yg+'" x2="'+(ML+PW)+'" y2="'+yg+'" stroke="#eee"/><text x="'+(ML-6)+'" y="'+(yg+4)+'" font-size="10" fill="#888" text-anchor="end">'+g.toFixed(1)+'</text>';}
        var tstep=T>=50?10:5; for(var tt=0;tt<=T;tt+=tstep){h+='<text x="'+sx(tt)+'" y="'+(MT+PH+14)+'" font-size="10" fill="#888" text-anchor="middle">'+tt+'</text>';}
        for(i=0;i<N;i+=2){var tr2=S.trajs[i],p='M'+sx(0).toFixed(1)+','+sy(tr2[0]).toFixed(1);for(t=1;t<tr2.length;t++)p+='L'+sx(t).toFixed(1)+','+sy(tr2[t]).toFixed(1);
          h+='<path d="'+p+'" fill="none" stroke="'+(Ns[i]>0?'#e67e22':'#1565c0')+'" stroke-opacity="'+(Ns[i]>0?0.55:0.22)+'" stroke-width="1"/>';}
        h+='<line x1="'+ML+'" y1="'+sy(XG)+'" x2="'+(ML+PW)+'" y2="'+sy(XG)+'" stroke="#2e7d32" stroke-dasharray="5,3" stroke-width="1.3"/>';
        h+='<line x1="'+ML+'" y1="'+sy(XB)+'" x2="'+(ML+PW)+'" y2="'+sy(XB)+'" stroke="#c62828" stroke-width="2"/>';
        h+='<text x="'+(ML+PW-4)+'" y="'+(sy(XB)-5)+'" font-size="10.5" fill="#c62828" text-anchor="end">boundary x = 1 (unsafe above)</text>';
        h+='<text x="'+(ML+PW-4)+'" y="'+(sy(XG)+13)+'" font-size="10.5" fill="#2e7d32" text-anchor="end">goal x = 0.8</text>';
        h+='<line x1="'+ML+'" y1="'+MT+'" x2="'+ML+'" y2="'+(MT+PH)+'" stroke="#333" stroke-width="1.5"/><line x1="'+ML+'" y1="'+(MT+PH)+'" x2="'+(ML+PW)+'" y2="'+(MT+PH)+'" stroke="#333" stroke-width="1.5"/>';
        h+='<text x="'+(ML+PW/2)+'" y="'+(H-3)+'" font-size="11" fill="#444" text-anchor="middle">time step t</text>';
        h+='<text x="12" y="'+(MT+PH/2)+'" font-size="11" fill="#444" text-anchor="middle" transform="rotate(-90,12,'+(MT+PH/2)+')">state x</text>';
        h+='<line x1="'+(ML+8)+'" y1="'+(MT+10)+'" x2="'+(ML+28)+'" y2="'+(MT+10)+'" stroke="#1565c0" stroke-width="2"/><text x="'+(ML+32)+'" y="'+(MT+14)+'" font-size="10.5" fill="#444">never violates</text>';
        h+='<line x1="'+(ML+118)+'" y1="'+(MT+10)+'" x2="'+(ML+138)+'" y2="'+(MT+10)+'" stroke="#e67e22" stroke-width="2"/><text x="'+(ML+142)+'" y="'+(MT+14)+'" font-size="10.5" fill="#444">violates at least once ('+nv+' of 200)</text>';
        $('ls-ce-svg1').innerHTML=h;
        // ---- plot 2: histogram of Z
        var W2=700,H2=190,ML2=44,MR2=14,MT2=14,MB2=32,PW2=W2-ML2-MR2,PH2=H2-MT2-MB2;
        var zlo=Math.min(-0.3,Math.min.apply(null,Zs)-0.02), zhi=Math.max(0.3,zmax+0.02), nb=36, bw=(zhi-zlo)/nb, cnt=[], cmax=1;
        for(i=0;i<nb;i++)cnt.push(0); for(i=0;i<N;i++){var b=Math.min(nb-1,Math.floor((Zs[i]-zlo)/bw));cnt[b]++;if(cnt[b]>cmax)cmax=cnt[b];}
        function zx(z){return ML2+(z-zlo)/(zhi-zlo)*PW2;} function cy(c){return MT2+PH2*(1-c/cmax);}
        var h2='';
        for(i=0;i<nb;i++){var z0=zlo+i*bw,z1=z0+bw,mid=0.5*(z0+z1);h2+='<rect x="'+zx(z0).toFixed(1)+'" y="'+cy(cnt[i]).toFixed(1)+'" width="'+(zx(z1)-zx(z0)-0.6).toFixed(1)+'" height="'+(cy(0)-cy(cnt[i])).toFixed(1)+'" fill="'+(mid>0?'#c62828':'#1565c0')+'" fill-opacity="0.55"/>';}
        var zs2=(zhi-zlo)>2?0.5:(zhi-zlo)>0.8?0.2:0.1;
        for(g=Math.ceil(zlo/zs2)*zs2;g<=zhi+1e-9;g+=zs2){h2+='<text x="'+zx(g)+'" y="'+(MT2+PH2+14)+'" font-size="10" fill="#888" text-anchor="middle">'+g.toFixed(1)+'</text>';}
        h2+='<line x1="'+ML2+'" y1="'+(MT2+PH2)+'" x2="'+(ML2+PW2)+'" y2="'+(MT2+PH2)+'" stroke="#333" stroke-width="1.5"/>';
        h2+='<text x="'+(ML2-6)+'" y="'+(MT2+4)+'" font-size="10" fill="#888" text-anchor="end">'+cmax+'</text><text x="'+(ML2-6)+'" y="'+(MT2+PH2+4)+'" font-size="10" fill="#888" text-anchor="end">0</text>';
        function vline(z,col,dash,lab,dy){if(z<zlo||z>zhi)return '';return '<line x1="'+zx(z)+'" y1="'+MT2+'" x2="'+zx(z)+'" y2="'+(MT2+PH2)+'" stroke="'+col+'" stroke-width="1.6"'+(dash?' stroke-dasharray="5,3"':'')+'/><text x="'+(zx(z)+4)+'" y="'+(MT2+dy)+'" font-size="10.5" fill="'+col+'">'+lab+'</text>';}
        h2+=vline(0,'#c62828',false,'0',12)+vline(zmean,'#888',true,'mean '+f(zmean,2),12)+vline(va,'#7b1fa2',true,'VaR '+f(va,2),26)+vline(cv,'#7b1fa2',false,'CVaR '+f(cv,2),40);
        h2+='<text x="'+(ML2+PW2/2)+'" y="'+(H2-3)+'" font-size="11" fill="#444" text-anchor="middle">signed maximum excursion Z = max_t (x_t - 1) per episode (red = crossed the boundary)</text>';
        h2+='<text x="12" y="'+(MT2+PH2/2)+'" font-size="11" fill="#444" text-anchor="middle" transform="rotate(-90,12,'+(MT2+PH2/2)+')">episodes</text>';
        $('ls-ce-svg2').innerHTML=h2;
      }
      globalThis.__ceAPI = {Q:Q,exactEN:exactEN,noise:noise,simulate:simulate,
        cvar:cvar,varA:varA,fp:fp,mulberry32:mulberry32,gauss:gauss};
      ['ls-ce-k','ls-ce-sig','ls-ce-T','ls-ce-alpha','ls-ce-d','ls-ce-delta'].forEach(function(id){$(id).addEventListener('input',draw);});
      $('ls-ce-resample').addEventListener('click',function(){seedNo++;draw();});
      draw();
    })();