"""Prepare solution-depth decisions for the Gaussian-process toolkit."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
source=ROOT/'book/solutions/baseline-source90/pages/toolkit-gp.html.json'
baseline=json.loads(source.read_bytes())
replacements={};rationales={}

def replace(key,reason,body):
    replacements[key]=body.strip()+'\n';rationales[key]=reason

replace('book-m3-b1','Derives the repeated-reading solve, latent variance and temperature decision in the all-ones eigendirection, with units and exact threshold.',r'''
<p><strong>1. Use the repeated-location structure.</strong> Let $\mathbf1=(1,1,1)^\top$. The Gram matrix is $K=4\mathbf1\mathbf1^\top$, the readings are $y=2\mathbf1$, and $\lambda=1$ squared degree. Since $\mathbf1^\top\mathbf1=3$, $(K+I)\mathbf1=(4\cdot3+1)\mathbf1=13\mathbf1$. Thus the solve $(K+I)\alpha=y$ gives $\alpha=(2/13)\mathbf1$. The matrix is invertible because $K$ is PSD and $I$ is positive definite.</p>
<p><strong>2. Compute the latent posterior at that location.</strong> Its covariance vector is $k_a=4\mathbf1$. Therefore $\mu(a)=k_a^\top\alpha=4\cdot3\cdot(2/13)=24/13$ degrees. For the variance, solve $(K+I)v=k_a$, obtaining $v=(4/13)\mathbf1$. Then $\sigma^2(a)=4-k_a^\top v=4-4\cdot3\cdot(4/13)=4-48/13=4/13$ squared degrees. Hence $\sigma(a)=2/\sqrt{13}$ degrees.</p>
<p><strong>3. Apply the supplied decision envelope.</strong> The upper residual is $\mu+2\sigma=24/13+4/\sqrt{13}\approx2.955554$ degrees. Adding the nominal temperature gives $57+24/13+4/\sqrt{13}\approx59.955554\le60$ degrees, so the proposal passes on the explicitly assumed confidence event. Independent noisy repeats reduce the variance while the mean approaches the repeated reading, $2$ degrees. These three readings define a different dataset from the two-location midpoint example; combining the datasets requires a new joint solve.</p>
''')
replace('practice-8','Shows every scalar substitution and keeps the evaluated band conditional on the theorem assumptions.',r'''
<p><strong>1. Evaluate the noise scaling and logarithm.</strong> The regularizer has $\sqrt\lambda=\sqrt{0.04}=0.2$, so $R/\sqrt\lambda=0.1/0.2=1/2$. Also $1/\delta=20$, and $2\log20\approx5.9914645$.</p>
<p><strong>2. Substitute into the multiplier.</strong> With the supplied realized log determinant $3$ and $B=2$,</p>
<div class="math-block">$$\beta=2+\frac12\sqrt{3+2\log20}\approx2+\frac12\sqrt{8.9914645}\approx3.4992885.$$</div>
<p><strong>3. Convert the multiplier into a half-width.</strong> At $\sigma(x)=0.2$, $\beta\sigma(x)=0.2[2+(1/2)\sqrt{3+2\log20}]\approx0.6998577$. The norm contribution is $B\sigma=0.4$ and the remaining approximately $0.2998577$ comes from noise concentration. The interval would be $[\mu(x)-0.6998577,\mu(x)+0.6998577]$, up to the displayed rounding.</p>
<p>This arithmetic applies the valid-bound formula; it does not establish its assumptions. They include a fixed function with RKHS norm at most $B$, the conditional $R$-sub-Gaussian noise bound, predictable query choices and the matching positive regularizer. A multiplier computed using an unjustified $B$ does not inherit the theorem's probability.</p>
''')
replace('practice-9','Proves the minimum using a lower bound and an explicit attaining interpolant rather than relying on an unstated projection result.',r'''
<p><strong>1. Derive a lower bound on any interpolating function.</strong> Let $h=k(a,\cdot)-k(b,\cdot)$. The reproducing property gives $\langle f,h\rangle_k=f(a)-f(b)=2$. Its squared norm is $k(a,a)-2k(a,b)+k(b,b)=2(1-r)$. Cauchy–Schwarz therefore yields $4\le\|f\|_k^2\,2(1-r)$, hence $\|f\|_k^2\ge2/(1-r)$. Division is valid because $r\lt1$.</p>
<p><strong>2. Attain that lower bound.</strong> Define $f_\star=h/(1-r)$. Since $h(a)=1-r$ and $h(b)=r-1$, this function has $f_\star(a)=1$ and $f_\star(b)=-1$. Its squared norm is $\|h\|_k^2/(1-r)^2=2/(1-r)$, so it attains the bound and is a minimum-norm interpolant. Equivalently, for $y=(1,-1)^\top$ the Gram relation $Ky=(1-r)y$ gives coefficients $K^{-1}y=y/(1-r)$ and the same squared norm $y^\top K^{-1}y$.</p>
<p><strong>3. Evaluate and interpret.</strong> At $r=0.5$, the minimum squared norm is $2/0.5=4$, giving norm $2$. At $r=0.99$, it is $2/0.01=200$, giving norm $\sqrt{200}\approx14.1421$. Highly correlated inputs make their kernel sections nearly equal; forcing their evaluations to differ by $2$ consequently requires a large function norm.</p>
''')
replace('practice-10','Writes the three-term decomposition explicitly, justifies the triangle inequality, and shows both numerical contributions and the fixed-n limit.',r'''
<p><strong>1. Insert the two intermediate functions.</strong> At the same input $x$, write $f^*-\mu^*=(f^*-\tilde f)+(\tilde f-\mu)+(\mu-\mu^*)$. Applying the triangle inequality and then the three given bounds gives</p>
<div class="math-block">$$|f^*(x)-\mu^*(x)|\le\epsilon+\beta\sigma(x)+\epsilon\sqrt{n/\lambda}\,\sigma(x)=\epsilon+\left(\beta+\epsilon\sqrt{n/\lambda}\right)\sigma(x).$$</div>
<p><strong>2. Evaluate the terms.</strong> Here $n/\lambda=16/0.25=64$ and its square root is $8$. The direct model mismatch is $0.05$, the original statistical half-width is $2(0.1)=0.2$, and the shift of the fitted mean contributes $0.05(8)(0.1)=0.04$. Adding gives $0.05+0.2+0.04=0.29$.</p>
<p><strong>3. Interpret the floor.</strong> For fixed $n$ and $\lambda$, as $\sigma(x)$ tends to zero the displayed upper bound tends to $\epsilon=0.05$. The original $0.2$ statistical term omitted both model-mismatch contributions. This is a floor in the available certificate, not a claim that the actual error must be at least $0.05$. The three inequalities remain assumptions whose model-mismatch justification must be supplied separately.</p>
''')
replace('practice-12','Shows elimination for both posterior solves, the final dot products and the covariance consistency calculation.',r'''
<p><strong>1. Solve for the data coefficients.</strong> Adding $\lambda I$ gives $M=\begin{bmatrix}3/2&1/2\\1/2&3/2\end{bmatrix}$. Multiplying by $(1,-1)^\top$ gives $(3/2-1/2,1/2-3/2)^\top=(1,-1)^\top=y$, so $\alpha=(1,-1)^\top$. The eigenvalues of $M$ are $2$ and $1$, both positive, ensuring the solve is unique.</p>
<p><strong>2. Solve for the query coefficients.</strong> Multiplying the equations $Mv=(1/2,0)^\top$ by $2$ gives $3v_1+v_2=1$ and $v_1+3v_2=0$. The second yields $v_1=-3v_2$; substitution into the first gives $-9v_2+v_2=1$, hence $v_2=-1/8$ and $v_1=3/8$.</p>
<p><strong>3. Form the posterior quantities.</strong> The mean is $\mu(x)=k_x^\top\alpha=(1/2)(1)+0(-1)=1/2$. The latent variance is $\sigma^2(x)=1-k_x^\top v=1-(1/2)(3/8)=13/16=0.8125$.</p>
<p><strong>4. Check that the proposed covariance is possible.</strong> The unregularized inverse is $K^{-1}=\begin{bmatrix}4/3&-2/3\\-2/3&4/3\end{bmatrix}$, so $k_x^\top K^{-1}k_x=(1/2)^2(4/3)=1/3$. The full latent covariance's Schur complement is $1-1/3=2/3\gt0$. Thus the given query covariance is consistent with a positive definite joint covariance. The actual posterior computation needed only the two solves, not an explicit inverse.</p>
''')
replace('::exercise-15','Defines the kernel-section vector, proves the exponential inequality with single-variable calculus, and handles the equality degeneracy.',r'''
<p><strong>(a) Convert an evaluation difference into an inner product.</strong> Write $\varphi(x)=k(x,\cdot)\in\mathcal H_k$. The reproducing property says $f(x)=\langle f,\varphi(x)\rangle_k$. Subtracting at the two inputs gives $f(x)-f(x')=\langle f,\varphi(x)-\varphi(x')\rangle_k$, so Cauchy–Schwarz bounds its absolute value by $\|f\|_k\|\varphi(x)-\varphi(x')\|_k$. Expand the squared second factor:</p>
<div class="math-block">$$\|\varphi(x)-\varphi(x')\|_k^2=k(x,x)-2k(x,x')+k(x',x')=d_k^2(x,x').$$</div>
<p>This proves the requested inequality. The square root is real because it is a squared Hilbert-space norm; $d_k$ can be zero for distinct inputs when their kernel sections coincide.</p>
<p><strong>(b) Convert the kernel distance into Euclidean distance.</strong> For the unit-amplitude SE kernel, let $r=\|x-x'\|_2$ and $a=r^2/(2\ell^2)$, with $\ell\gt0$. Then $d_k^2=2(1-e^{-a})$. To justify $1-e^{-a}\le a$, consider $g(a)=a-1+e^{-a}$: $g(0)=0$ and $g'(a)=1-e^{-a}\ge0$ for $a\ge0$. Hence $d_k^2\le2a=r^2/\ell^2$, so $d_k\le r/\ell$. Substitution into part (a) gives $|f(x)-f(x')|\le(B/\ell)\|x-x'\|_2$. Thus every function in the assumed norm ball is $B/\ell$-Lipschitz.</p>
<p><strong>(c) Identify equality in part (a).</strong> If $\varphi(x)=\varphi(x')$, both sides are zero for every $f$. Otherwise equality in Cauchy–Schwarz holds exactly when $f=c[\varphi(x)-\varphi(x')]$ for a real scalar $c$, including $c=0$. Indeed its evaluation difference has absolute value $|c|d_k^2$ and its norm is $|c|d_k$, so the two sides agree. This establishes sharpness of part (a); it does not require equality in the additional SE-to-Euclidean estimate of part (b).</p>
''')
replace('::exercise-16','Performs the block inverse and completed-square derivation, treats degenerate conditional variance, and distinguishes decreasing variance from nested intervals.',r'''
<p><strong>(a) Set up the joint Gaussian.</strong> Use a fixed kernel and independent Gaussian observation noise of working variance $\lambda\gt0$. Let $A=K_t+\lambda I$, $q=(k(x_i,x))_{i=1}^t$, and $c=k(x,x)$. The zero-mean joint vector $(y_t,f(x))$ has covariance $\Sigma=\begin{bmatrix}A&q\\q^\top&c\end{bmatrix}$. The observation block $A$ is positive definite. Put $s=c-q^\top A^{-1}q$, the nonnegative Schur complement.</p>
<p>If $s\gt0$, the block-inverse formula is</p>
<div class="math-block">$$\Sigma^{-1}=\begin{bmatrix}A^{-1}+A^{-1}qs^{-1}q^\top A^{-1}&-A^{-1}qs^{-1}\\-s^{-1}q^\top A^{-1}&s^{-1}\end{bmatrix}.$$</div>
<p>For joint values $(u,v)$, multiplication and completion of the square give $[u^\top,v]\Sigma^{-1}[u^\top,v]^\top=u^\top A^{-1}u+(v-q^\top A^{-1}u)^2/s$. Once $u=y_t$ is fixed, the first term is constant. The conditional density in $v$ is therefore Gaussian with mean $q^\top A^{-1}y_t$ and variance $s$. This derives $\mu_t(x)=q^\top(K_t+\lambda I)^{-1}y_t$ and $\sigma_t^2(x)=k(x,x)-q^\top(K_t+\lambda I)^{-1}q$.</p>
<p>If $s=0$, no density inverse is available for the whole joint covariance. Instead the Gaussian residual $f(x)-q^\top A^{-1}y_t$ has mean zero and variance $s=0$, so it equals zero almost surely. The same formulas give a degenerate conditional Gaussian, with exactly determined value.</p>
<p><strong>(b) Condition once more using the current posterior as the prior.</strong> After $t-1$ observations, the covariance is $k_{t-1}$. A fresh noisy observation at $x_t$ has variance $a=k_{t-1}(x_t,x_t)+\lambda\gt0$. Its covariance with the pair $(f(x),f(x'))$ is the column $(k_{t-1}(x_t,x),k_{t-1}(x_t,x'))^\top$. Applying the same Schur complement with the scalar observation block $a$ gives</p>
<div class="math-block">$$k_t(x,x')=k_{t-1}(x,x')-\frac{k_{t-1}(x,x_t)k_{t-1}(x_t,x')}{k_{t-1}(x_t,x_t)+\lambda}.$$</div>
<p>Setting $x'=x$ makes the numerator $k_{t-1}(x,x_t)^2\ge0$. The positive denominator then implies $\sigma_t^2(x)\le\sigma_{t-1}^2(x)$ for every query $x$. This comparison holds for a fixed kernel and regularizer regardless of the observed value. For a fixed multiplier the interval width decreases, but its center can move, so the raw intervals need not be nested. SafeOpt's intersections $C_t=C_{t-1}\cap Q_t$ are nested by construction, even when the multiplier grows.</p>
''')
replace('::exercise-17','Proves reduction to the data span and function uniqueness even with a singular Gram matrix, then derives both regularization limits with explicit remainder control.',r'''
<p><strong>(a) Reduce the function problem to its data span.</strong> Let $\mathcal S$ be the finite-dimensional span of $k(x_i,\cdot)$. Decompose any $f=s+h$ with $s\in\mathcal S$ and $h\perp\mathcal S$. Reproduction gives $h(x_i)=\langle h,k(x_i,\cdot)\rangle_k=0$, while Pythagoras gives $\|f\|_k^2=\|s\|_k^2+\|h\|_k^2$. For $\lambda\gt0$, adding $h$ leaves the data errors unchanged and increases the objective by $\lambda\|h\|_k^2$. Every minimizer therefore lies in $\mathcal S$.</p>
<p>Write $s=\sum_i\alpha_i k(x_i,\cdot)$. The evaluation vector is $K_t\alpha$, and the squared norm is $\alpha^\top K_t\alpha$. Expanding the objective gives</p>
<div class="math-block">$$J(\alpha)=y_t^\top y_t-2\alpha^\top K_ty_t+\alpha^\top K_t(K_t+\lambda I)\alpha.$$</div>
<p>The gradient is $2K_t[(K_t+\lambda I)\alpha-y_t]$, so $\alpha_0=(K_t+\lambda I)^{-1}y_t$ is stationary. The eigenvalues of $K_t(K_t+\lambda I)$ are $a_j(a_j+\lambda)\ge0$, where $a_j\ge0$ are the Gram eigenvalues. Hence $J$ is convex and this is a global minimizer. More explicitly $J(\alpha_0+\eta)-J(\alpha_0)=\eta^\top K_t(K_t+\lambda I)\eta\ge0$. Equality requires $K_t\eta=0$, whose represented function has squared norm $\eta^\top K_t\eta=0$ and is zero. Thus coefficients may be nonunique for singular $K_t$, but the minimizing function is unique. Its value at any query is $\mu_t(x)=k_t(x)^\top\alpha_0$.</p>
<p><strong>(b) Small regularization.</strong> If $K_t\succ0$, its eigenvalues $a_j$ are positive, and $1/(a_j+\lambda)$ tends to $1/a_j$ as $\lambda\downarrow0$. Thus the coefficient vector tends to $K_t^{-1}y_t$, and the functions converge in the finite data span to $s_t(x)=k_t(x)^\top K_t^{-1}y_t$. It interpolates because $K_tK_t^{-1}y_t=y_t$. Every other interpolating function differs by a function perpendicular to the data span, so Pythagoras proves this is the minimum-norm interpolant, with squared norm $y_t^\top K_t^{-1}y_t$.</p>
<p><strong>Large regularization.</strong> For fixed data and Gram matrix, the scalar identity</p>
<div class="math-block">$$\frac1{\lambda+a_j}=\frac1\lambda-\frac{a_j}{\lambda^2}+\frac{a_j^2}{\lambda^2(\lambda+a_j)}$$</div>
<p>has a remainder at most $a_j^2/\lambda^3$. Reassembling in an orthonormal eigenbasis gives $(K_t+\lambda I)^{-1}=\lambda^{-1}I-\lambda^{-2}K_t+O(\lambda^{-3})$. Multiplication yields $\mu_t(x)=\lambda^{-1}k_t(x)^\top y_t+O(\lambda^{-2})\to0$ and $\sigma_t^2(x)=k(x,x)-\lambda^{-1}\|k_t(x)\|_2^2+O(\lambda^{-2})\to k(x,x)$. Here the remainder constants can depend on the fixed query, data and kernel. Heavy regularization approaches the prior mean and variance because the observations receive less weight.</p>
''')

retained={
'book-m3-b2':'Carries the exact midpoint envelope plus discrepancy into both the old temperature test and solved maximum nominal temperature, and explains the systematic-error assumption.',
'practice-1':'Displays the Gram matrix, eigen-directions, both function evaluations and every term of the RKHS norm quadratic form.',
'practice-2':'Substitutes all scalar posterior mean/variance factors at both queries and distinguishes latent and fresh-observation variances.',
'practice-3':'Takes the square root, calculates the half-width and endpoints, compares the threshold and demonstrates the variance-substitution error.',
'practice-4':'Matches both defining conventions, takes their square roots and distinguishes norm and multiplier assumptions.',
'practice-5':'Calculates the power function, interpolation prediction and error bound at both locations, and explains deterministic scope.',
'practice-6':'Gives and verifies the all-ones solve and variance subtraction, evaluates both n values and explains why independent noisy repeats differ from exact repeats.',
'practice-7':'Adds one to each Gram eigenvalue, computes the determinant/logarithm and explains why one design only bounds the maximum from below.',
'practice-11':'Shows the partial-fraction telescoping sum, finite union bound and increasing-event limit; the constant-budget counterexample is explained.',
'::exercise-18':'Derives the finite-feature determinant, trace budget, concavity bound, equality conditions, repeated-basis design and rank obstruction; additionally derives and attains the correct T<d maximum.',
'::exercise-19':'Translates both norm conventions, displays both multiplier substitutions, distinguishes the two regularizers and derives variance monotonicity in an eigenbasis to explain actual width comparison.',
'::exercise-20':'Compares both eigenvalue/logarithm factors, computes noise terms, derives every rescaling identity and gives a concrete zero-function Gaussian failure with explicit coverage formula; it correctly distinguishes lack of scale equivariance from proof of invalidity.',
}
rows=[]
for ex in baseline['exercises']:
    key=ex['anchor'] if ex['anchor'] is not None else '::exercise-'+str(ex['ordinal'])
    assert key in replacements or key in retained,key
    row={'inventory_key':ex['inventory_key'],'source_file':ex['source_file'],
         'original_solution_sha256':ex['solution']['sha256'],
         'decision':'replace' if key in replacements else 'retain',
         'thoroughness_rationale':rationales.get(key,retained.get(key))}
    if key in replacements:row['replacement_html']=replacements[key]
    rows.append(row)
data=(json.dumps({'status':'all20_authored_pending_independent_semantic_review',
                 'baseline_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                 'exercises':rows},indent=2,ensure_ascii=False)+'\n').encode()
out=ROOT/'book/solutions/drafts/toolkit-gp-thorough-solutions-v1.json'
if out.exists() and out.read_bytes()!=data:raise RuntimeError('Draft is immutable')
out.write_bytes(data)
print(json.dumps({'draft':str(out.relative_to(ROOT)),'total':len(rows),'replace':len(replacements),'retain':len(retained),'sha256':hashlib.sha256(data).hexdigest()}))
