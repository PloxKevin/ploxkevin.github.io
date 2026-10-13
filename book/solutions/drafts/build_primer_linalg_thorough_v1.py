"""Prepare reviewed, solution-body-only linear algebra teaching drafts."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
baseline = json.loads((ROOT / 'book/solutions/baseline-source90/pages/primer-linalg.html.json').read_text())
replacements = {}
reasons = {}

def replace(key, reason, body):
    replacements[key] = body.strip() + '\n'
    reasons[key] = reason

replace('la-ex-norms-3', 'Shows the infimum argument without assuming an unexplained nearest-point theorem, proves both inequality directions, and verifies the radial minimizer and displaced interval.', r'''
<p><strong>1. Turn the definition into an inequality.</strong> Write $d_x=\inf_{c\in C}\|x-c\|$ and $d_y=\inf_{c\in C}\|y-c\|$. These are finite nonnegative numbers because $C$ is nonempty. For any $\varepsilon\gt0$, the definition of infimum supplies $c_\varepsilon\in C$ with $\|y-c_\varepsilon\|\lt d_y+\varepsilon$. The triangle inequality gives</p>
<div class="math-block">$$d_x\le\|x-c_\varepsilon\|\le\|x-y\|+\|y-c_\varepsilon\|\lt\|x-y\|+d_y+\varepsilon.$$</div>
<p>This holds for every positive $\varepsilon$, so $d_x-d_y\le\|x-y\|$. Otherwise choosing $\varepsilon$ smaller than the positive gap would contradict the displayed bound. Interchanging $x$ and $y$ gives $d_y-d_x\le\|x-y\|$. The two bounds together say $|d_x-d_y|\le\|x-y\|$. This proof works even without closedness; for the closed finite-dimensional set in the question one could instead use an actual nearest point as suggested by the hint.</p>
<p><strong>2. Compute the distance to the disc.</strong> The point $x=(3,4)$ has length $5$. Every point $c$ in the closed unit disc has $\|c\|_2\le1$, so the reverse triangle inequality gives $\|x-c\|_2\ge5-1=4$. The point $c=(3/5,4/5)$ lies on the unit circle, and $x-c=(12/5,16/5)$ has length $\sqrt{144+256}/5=4$. A lower bound and a point attaining it prove that the distance is exactly $4$.</p>
<p><strong>3. Carry the displacement bound through the theorem.</strong> If $\|x'-x\|_2\le0.1$, then $|\operatorname{dist}(x',C)-4|\le0.1$. Hence the new distance lies in $[3.9,4.1]$. The displacement direction need not be known.</p>
''')
replace('la-ex-matrix-norms-3', 'Derives the finite geometric remainder, compares its diagonal entries, and makes the term-count inequality explicit.', r'''
<p><strong>1. Sum each diagonal entry.</strong> Here $A=\operatorname{diag}(1/2,1/4)$, so $A^t=\operatorname{diag}((1/2)^t,(1/4)^t)$. For a scalar $r\ne1$, multiplying $1+r+\cdots+r^{T-1}$ by $1-r$ cancels every middle term and leaves $1-r^T$. Therefore</p>
<div class="math-block">$$\sum_{t=0}^{T-1}A^t=\operatorname{diag}\left(2[1-2^{-T}],\frac43[1-4^{-T}]\right).$$</div>
<p>Both powers tend to zero as $T$ grows. Thus the infinite sum is $\operatorname{diag}(2,4/3)=(I-A)^{-1}$, and subtracting the finite sum gives the exact remainder $\operatorname{diag}(2^{1-T},(4/3)4^{-T})$.</p>
<p><strong>2. Take the spectral norm.</strong> A diagonal matrix stretches coordinate axes by the absolute values of its diagonal entries, so its spectral norm is the larger one. Their ratio is $2^{1-T}/[(4/3)4^{-T}]=(3/2)2^T\ge1$ for $T\ge0$. The remainder norm is consequently $2^{1-T}$.</p>
<p><strong>3. Find the first acceptable integer.</strong> The tolerance requires $2^{1-T}\le0.01$, equivalently $2^T\ge200$. Since $2^7=128\lt200$ and $2^8=256\ge200$, the smallest $T$ is $8$. This means the eight terms $A^0$ through $A^7$. The errors at $T=7$ and $T=8$ are respectively $1/64=0.015625$ and $1/128=0.0078125$, confirming the cutoff.</p>
''')
replace('la-ex-psd-2', 'Matches every Cholesky entry, displays forward and backward substitution, and derives the determinant from the positive pivots.', r'''
<p><strong>1. Construct the factor.</strong> Seek a lower triangular matrix $L=\begin{bmatrix}\ell_{11}&0\\\ell_{21}&\ell_{22}\end{bmatrix}$ with positive diagonal and $LL^\top=P=\begin{bmatrix}4&2\\2&2\end{bmatrix}$. Multiplication gives the three equations $\ell_{11}^2=4$, $\ell_{11}\ell_{21}=2$, and $\ell_{21}^2+\ell_{22}^2=2$. Solving in that order gives $\ell_{11}=2$, $\ell_{21}=1$, and $\ell_{22}=1$. Hence $L=\begin{bmatrix}2&0\\1&1\end{bmatrix}$.</p>
<p><strong>2. Solve $Px=(6,4)^\top$ without forming an inverse.</strong> Because $P=LL^\top$, first solve $Ly=(6,4)^\top$: $2y_1=6$ gives $y_1=3$, and $y_1+y_2=4$ gives $y_2=1$. Next solve $L^\top x=y$: the bottom equation is $x_2=1$, and the top is $2x_1+x_2=3$, giving $x_1=1$. Thus $x=(1,1)$; direct multiplication gives $Px=(4+2,2+2)=(6,4)$.</p>
<p><strong>3. Read the determinant from the factor.</strong> The determinant of a triangular matrix is the product of its diagonal entries. Therefore $\det P=(\det L)^2=(2\cdot1)^2=4$, and $\log\det P=2(\log2+\log1)=\log4$. The positive pivots also make $L$ invertible, so $x^\top Px=\|L^\top x\|_2^2\gt0$ for every nonzero $x$: the factor verifies positive definiteness.</p>
''')
replace('la-ex-psd-3', 'Transforms the ellipsoid to a unit ball, derives the support bound and equality direction, and checks feasibility and the objective.', r'''
<p><strong>1. Remove the unequal coordinate scales.</strong> The constraint is $4x_1^2+x_2^2\le1$. Set $u=(2x_1,x_2)$; then $\|u\|_2\le1$, $x_1=u_1/2$, and $x_2=u_2$. The objective becomes $x_1+2x_2=(1/2,2)^\top u$.</p>
<p><strong>2. Find an upper bound and attain it.</strong> With $w=(1/2,2)$, Cauchy–Schwarz gives $w^\top u\le\|w\|_2\|u\|_2\le\sqrt{1/4+4}=\sqrt{17}/2$. Equality holds at $u=w/\|w\|_2=(1,4)/\sqrt{17}$. Transforming back gives $x^\star=(1/(2\sqrt{17}),4/\sqrt{17})$.</p>
<p><strong>3. Check both claims.</strong> At this point $4(x_1^\star)^2+(x_2^\star)^2=1/17+16/17=1$, so it is feasible. Its objective is $1/(2\sqrt{17})+8/\sqrt{17}=17/(2\sqrt{17})=\sqrt{17}/2$, meeting the upper bound. The maximum is therefore exactly $\sqrt{17}/2$.</p>
<p>The ellipsoid has coordinate half-widths $1/2$ and $1$. The maximizing direction is proportional to $P^{-1}(1,2)^\top=(1/4,2)^\top$, where $P=\operatorname{diag}(4,1)$. The inverse weights compensate for the constraint's unequal scales; pointing along the Euclidean objective vector would not in general attain the bound.</p>
''')
replace('la-ex-blocks-2', 'Expands the completed square and proves necessity, sufficiency, strictness and the boundary null vector separately.', r'''
<p><strong>1. Complete the square.</strong> For $z=(x,y)$ the quadratic form is $ax^2+4xy+3y^2$. Since $3(y+2x/3)^2=3y^2+4xy+(4/3)x^2$, subtraction gives</p>
<div class="math-block">$$z^\top M(a)z=(a-4/3)x^2+3(y+2x/3)^2.$$</div>
<p><strong>2. Classify PSD.</strong> If $a\ge4/3$, both terms are nonnegative for every $z$, proving PSD. Conversely, choose $y=-2x/3$ so the second square vanishes. For $x\ne0$ the remaining value is negative when $a\lt4/3$. Thus PSD holds exactly for $a\ge4/3$.</p>
<p><strong>3. Classify PD and the boundary.</strong> If $a\gt4/3$ and $x\ne0$, the first term is positive. If $x=0$ but $z\ne0$, then $y\ne0$ and the second term is positive. This proves PD. At $a=4/3$, the nonzero vector $z=(3,-2)$ makes both terms zero, and direct multiplication gives $M(4/3)z=(4-4,6-6)=(0,0)$. The boundary is singular PSD, not PD. For $a\lt4/3$ this same vector gives the negative value $9(a-4/3)$.</p>
''')
replace('la-ex-blocks-3', 'Shows the entrywise inverse update and independent product check, keeping exact logarithms separate from rounded values.', r'''
<p><strong>1. Compute the quantities used by both update formulas.</strong> For $V=\operatorname{diag}(2,1)$, $V^{-1}=\operatorname{diag}(1/2,1)$. Thus $v=V^{-1}u=(1/2,2)$ and $u^\top v=1/2+4=9/2$. The denominator $1+u^\top v=11/2$ is positive, so the rank-one inverse formula applies.</p>
<p><strong>2. Update the determinant.</strong> The determinant lemma gives $\det(V+uu^\top)=\det V(1+u^\top V^{-1}u)=2(11/2)=11$. The increase in log determinant is $\log11-\log2=\log(11/2)\approx1.70475$, using natural logarithms.</p>
<p><strong>3. Update the inverse entry by entry.</strong> Sherman–Morrison gives $V^{-1}-vv^\top/(11/2)$. Here $vv^\top=\begin{bmatrix}1/4&1\\1&4\end{bmatrix}$. Its entries are $1/2-(2/11)(1/4)=5/11$, $0-(2/11)(1)=-2/11$, and $1-(2/11)(4)=3/11$. Therefore</p>
<div class="math-block">$$(V+uu^\top)^{-1}=\frac1{11}\begin{bmatrix}5&-2\\-2&3\end{bmatrix}.$$</div>
<p><strong>4. Verify independently.</strong> Adding $uu^\top$ gives $V+uu^\top=\begin{bmatrix}3&2\\2&5\end{bmatrix}$, whose direct determinant is $15-4=11$. Multiplication by the proposed inverse gives $\frac1{11}\begin{bmatrix}15-4&-6+6\\10-10&-4+15\end{bmatrix}=I$. Both update results pass direct checks.</p>
''')
replace('la-ex-structured-3', 'Shows the Cayley multiplication, explains invertibility for real skew-symmetric matrices, and proves the excluded minus-one eigenvalue rather than citing it.', r'''
<p><strong>1. Calculate this Cayley transform.</strong> For $A=\begin{bmatrix}0&-1\\1&0\end{bmatrix}$, the determinant of $I+A=\begin{bmatrix}1&-1\\1&1\end{bmatrix}$ is $2$, so $(I+A)^{-1}=\frac12\begin{bmatrix}1&1\\-1&1\end{bmatrix}$. Multiplying gives</p>
<div class="math-block">$$Q=(I-A)(I+A)^{-1}=\frac12\begin{bmatrix}1&1\\-1&1\end{bmatrix}\begin{bmatrix}1&1\\-1&1\end{bmatrix}=\begin{bmatrix}0&1\\-1&0\end{bmatrix}.$$</div>
<p>Its columns are perpendicular unit vectors, hence $Q^\top Q=I$. Also $\det Q=1$ and $Q(1,0)^\top=(0,-1)^\top$, so it is a clockwise $90$ degree rotation.</p>
<p><strong>2. Explain why $I+A$ is invertible for any real skew-symmetric $A$.</strong> Transposing the real scalar $w^\top Aw$ gives $w^\top A^\top w=-w^\top Aw$, so $w^\top Aw=0$. If $(I+A)w=0$, multiplying on the left by $w^\top$ gives $\|w\|_2^2+w^\top Aw=0$, and therefore $w=0$. A finite square matrix with trivial nullspace is invertible.</p>
<p><strong>3. Explain the missing rotation.</strong> Suppose $Qv=-v$ and put $w=(I+A)^{-1}v$, so $v=(I+A)w$. Substitution gives $(I-A)w=-(I+A)w$, or $w-Aw=-w-Aw$. Cancelling the $Aw$ terms leaves $2w=0$, hence $v=0$. Thus no nonzero vector can have eigenvalue $-1$ for a Cayley transform with a finite real skew parameter. In particular $-I$ cannot be represented this way. It can arise as a limit of parameters whose size tends to infinity, but no finite parameter attains it.</p>
''')
replace('book-a-ex-1', 'Derives both reconstructed coordinates and the true-state interval, checks attainment of the uncertainty endpoints, and explains the certification assumptions.', r'''
<p><strong>1. Reconstruct the central estimate.</strong> The calibrated model is $y=Hz+\eta$ with $H=\begin{bmatrix}1&1\\1&-1\end{bmatrix}$ and readings $y=(3,-1)^\top$ millimetres. Adding the two error-free reconstruction equations gives $2\hat z_1=3+(-1)=2$; subtracting gives $2\hat z_2=3-(-1)=4$. Thus $\hat z=(1,2)^\top$ millimetres.</p>
<p><strong>2. Propagate the sensor errors.</strong> Since $H^{-1}=H/2$, $\hat z-z=H\eta/2$. The first coordinate is $\hat z_1-z_1=(\eta_1+\eta_2)/2$. If each $|\eta_i|\le E$, the triangle inequality gives $|\hat z_1-z_1|\le(|\eta_1|+|\eta_2|)/2\le E$. Consequently the true displacement lies in $[1-E,1+E]$ millimetres. Equal extreme sensor errors attain both endpoints: for example $\eta_1=\eta_2=-E$ gives $z_1=1+E$.</p>
<p><strong>3. Compare the entire interval with the assembly limit.</strong> With $E=0.1$, the largest compatible $z_1$ is $1.1\gt1.05$ millimetres, so the limit cannot be certified. With $E=0.04$, every compatible value obeys $z_1\le1.04\le1.05$ millimetres, so the limit is certified. These conclusions use the stated calibration and additive-error bounds. The central estimate $1$ alone does not test every displacement consistent with the readings.</p>
''')
replace('book-a-ex-2', 'Parameterizes all real solutions, derives the unique minimum-length convention and the physical feasible interval, then supplies the limit counterexample.', r'''
<p><strong>1. Parameterize the measurements.</strong> The equation $z_1+z_2=6$ leaves one free coordinate. Write $z_1=3+t$; substitution forces $z_2=3-t$. Every real $t$ gives a solution, and every solution has this form.</p>
<p><strong>2. Minimize the length.</strong> Squaring the Euclidean norm gives $(3+t)^2+(3-t)^2=9+6t+t^2+9-6t+t^2=18+2t^2$. This is at least $18$, with equality only for $t=0$. Thus $(3,3)$ millimetres is the unique minimum-length solution. It is a choice among measurement-compatible states, not an additional measurement of the true state.</p>
<p><strong>3. Apply physical nonnegativity.</strong> The two inequalities become $3+t\ge0$ and $3-t\ge0$, respectively $t\ge-3$ and $t\le3$. Hence $t\in[-3,3]$ and $z_1=3+t$ ranges over $[0,6]$ millimetres.</p>
<p><strong>4. Test certification.</strong> The state $(5,1)$ has nonnegative coordinates and sums to $6$, yet $z_1=5\gt4$. It is a counterexample under both the unrestricted measurement model and its nonnegative restriction. The minimum-length estimate satisfies $z_1\le4$, but selecting that estimate does not certify the unknown physical displacement. An additional justified restriction or measurement must rule out the counterexample.</p>
''')
replace('book-a-ex-3', 'Carries the units through normalization, proves and verifies the attaining error direction, and distinguishes the coordinate box from the Euclidean ball.', r'''
<p><strong>1. Put the physical model into dimensionless coordinates.</strong> Substitute $p=(2\,\mathrm{mm})z_1$ and $v=(0.5\,\mathrm{mm/s})z_2$ into $y=p+(2\,\mathrm{s})v$. Seconds cancel in the second term, giving $y=(2z_1+z_2)\,\mathrm{mm}$. Therefore $\Delta y=(2\Delta z_1+\Delta z_2)\,\mathrm{mm}$.</p>
<p><strong>2. Bound the ball and attain the bound.</strong> With $w=(2,1)$, Cauchy–Schwarz gives $|w^\top\Delta z|\le\|w\|_2\|\Delta z\|_2\le0.1\sqrt{2^2+1^2}=0.1\sqrt5$. Thus the largest possible absolute prediction error is $0.1\sqrt5\,\mathrm{mm}\approx0.223607\,\mathrm{mm}$. Choose $\Delta z=0.1(2,1)/\sqrt5$. Its squared length is $0.01(4+1)/5=0.01$, and its output is $0.1(4+1)/\sqrt5=0.1\sqrt5$ millimetres. Negating the direction attains the negative extreme.</p>
<p><strong>3. Compare separate coordinate bounds.</strong> Replacing the ball by $|\Delta z_i|\le0.1$ gives $|\Delta y|\le2(0.1)+0.1=0.3$ millimetres. The box attains this at $(0.1,0.1)$, whose Euclidean length is $0.1\sqrt2\gt0.1$. It is therefore a valid but larger uncertainty set. The normalization scales define the geometry of the original ball; adding raw squared positions and velocities would mix incompatible units.</p>
''')
replace('book-a-ex-4', 'Displays the full normal-equation elimination, exact residual checks, a uniqueness proof from objective differences, and the particular-state error calculation.', r'''
<p><strong>1. Form the normal equations.</strong> Equal-weight least squares minimizes $\|y-Hz\|_2^2$. Differentiating with respect to $z$ gives $H^\top Hz=H^\top y$. Taking column dot products produces</p>
<div class="math-block">$$H^\top H=\begin{bmatrix}1+1+0&1+1.1+0\\1+1.1+0&1+1.21+1\end{bmatrix}=\begin{bmatrix}2&2.1\\2.1&3.21\end{bmatrix},\qquad H^\top y=\begin{bmatrix}6+6.2\\6+1.1(6.2)+2.1\end{bmatrix}=\begin{bmatrix}12.2\\14.92\end{bmatrix}.$$</div>
<p><strong>2. Solve by elimination.</strong> The equations are $2\hat z_1+2.1\hat z_2=12.2$ and $2.1\hat z_1+3.21\hat z_2=14.92$. Subtract $2.1$ times the first equation from $2$ times the second. The first-coordinate terms cancel, leaving $(6.42-4.41)\hat z_2=29.84-25.62$, so $2.01\hat z_2=4.22$. Hence $\hat z_2=422/201\approx2.09950249$. Back-substitution gives $\hat z_1=[12.2-2.1(422/201)]/2=261/67\approx3.89552239$ millimetres.</p>
<p><strong>3. Check residual orthogonality exactly.</strong> Use the convention $r=y-H\hat z$. With denominator $201$, $\hat z=(783,422)/201$. Therefore $r_1=6-1205/201=1/201$, $r_2=6.2-[783+(11/10)422]/201=-1/201$, and $r_3=2.1-422/201=1/2010$, all in millimetres. The column products are $r_1+r_2=0$ and $r_1+1.1r_2+r_3=(10-11+1)/2010=0$, proving $H^\top r=0$ without rounding error.</p>
<p><strong>4. Explain uniqueness.</strong> If $H\delta=0$, the third row forces $\delta_2=0$ and the first then forces $\delta_1=0$. Thus $H$ has independent columns. For any proposed change $\delta$, orthogonality gives $\|y-H(\hat z+\delta)\|_2^2=\|r-H\delta\|_2^2=\|r\|_2^2+\|H\delta\|_2^2$. This is strictly greater for every nonzero $\delta$, establishing the unique global minimum.</p>
<p><strong>5. Compare with the teaching state.</strong> The state $(4,2)$ predicts $(6,6.2,2)$, so the recorded perturbation is $(0,0,0.1)$ millimetres. The estimate error is $\hat z-(4,2)=(-21,20)/201=(-7/67,20/201)$ millimetres. Its norm is $\sqrt{21^2+20^2}/201=29/201\approx0.144279$ millimetres. Least squares distributes the discrepancy across the readings; this particular perturbation does not establish a worst-case comparison between arbitrary sensor designs.</p>
''')

# The seven original mixed exercises need their compressed computations expanded.
replace('::exercise-29', 'Works each dual-norm maximum by an upper bound plus a verified maximizer, and explains both radius conversions as ball containment.', r'''
<p><strong>(a) Compute the three norms.</strong> Absolute values give $\|w\|_1=1+2+2=5$ and $\|w\|_\infty=2$. Squaring gives $\|w\|_2=\sqrt{1+4+4}=3$. Thus $2\le3\le5\le3\sqrt3\approx5.196$, as required.</p>
<p><strong>(b) Box constraint, $p=\infty$.</strong> Each $|\delta_i|\le0.1$, so $w^\top\delta=\delta_1-2\delta_2+2\delta_3\le|\delta_1|+2|\delta_2|+2|\delta_3|\le0.5$. The corner $(0.1,-0.1,0.1)$ is feasible and has objective $0.1+0.2+0.2=0.5$.</p>
<p><strong>Euclidean constraint, $p=2$.</strong> Cauchy–Schwarz gives $w^\top\delta\le\|w\|_2\|\delta\|_2\le0.3$. Set $\delta=0.1w/3=(1,-2,2)/30$. Its norm is $3/30=0.1$, and $w^\top\delta=(1+4+4)/30=0.3$.</p>
<p><strong>Sum-of-magnitudes constraint, $p=1$.</strong> Each coefficient of $w$ has magnitude at most $2$, so $w^\top\delta\le2\sum_i|\delta_i|\le0.2$. Both $(0,-0.1,0)$ and $(0,0,0.1)$ have 1-norm $0.1$ and objective $0.2$. Each case supplies both an upper bound and attainment, which proves the maximum rather than just proposing a direction.</p>
<p><strong>(c) Convert the image certificate.</strong> For $784$ coordinates, $\|\delta\|_2^2=\sum_i\delta_i^2\le784\|\delta\|_\infty^2$, so $\|\delta\|_2\le28\|\delta\|_\infty$. Every perturbation with $\|\delta\|_\infty\le1/28$ therefore lies in the certified Euclidean radius-$1$ ball. The inherited infinity-norm radius is exactly $1/28\approx0.035714$; the rounded value $0.036$ would be slightly too large. Conversely an infinity-norm radius-$0.1$ box is contained in a Euclidean radius-$2.8$ ball. A Euclidean certificate of radius $2.8$ would thus suffice. These are conversions justified by containment; the classifier could have additional robustness beyond the stated certificate.</p>
''')
replace('::exercise-30', 'Derives mixed operator norms, the spectral-norm quadratic equation, numerical bound checks and the nonsymmetric eigenvalue comparison.', r'''
<p><strong>1. Compute the entry-based norms.</strong> The absolute column sums are $1+3=4$ and $2+4=6$, so $\|B\|_1=6$. The absolute row sums are $1+2=3$ and $3+4=7$, so $\|B\|_\infty=7$. Squaring all entries gives $\|B\|_F=\sqrt{1+4+9+16}=\sqrt{30}$.</p>
<p><strong>2. Compute the two mixed norms.</strong> For a Euclidean unit input, Cauchy–Schwarz bounds each output coordinate by its row's Euclidean length. The row lengths are $\sqrt5$ and $5$, so $\|B\|_{2\to\infty}\le5$. At $x=(3/5,4/5)$ the second output is $3(3/5)+4(4/5)=5$, proving equality. For an input with $\|x\|_1\le1$, every output magnitude is at most $4\|x\|_1$ because the largest entry magnitude is $4$. The input $(0,1)$ gives output $(-2,4)$ and attains $4$. Hence $\|B\|_{1\to\infty}=4$.</p>
<p><strong>3. Compute the spectral norm from a symmetric matrix.</strong> Multiplication gives $B^\top B=\begin{bmatrix}10&10\\10&20\end{bmatrix}$. Its characteristic equation is $(10-\lambda)(20-\lambda)-100=\lambda^2-30\lambda+100=0$. The roots are $[30\pm\sqrt{900-400}]/2=15\pm5\sqrt5$. Singular values are their positive square roots, so $\|B\|_2=\sqrt{15+5\sqrt5}\approx5.117$ and $\sigma_2=\sqrt{15-5\sqrt5}\approx1.954$. Their product is $\sqrt{225-125}=10=|\det B|$.</p>
<p><strong>4. Check the requested bounds.</strong> The two upper bounds are $\sqrt{30}\approx5.477$ and $\sqrt{6\cdot7}=\sqrt{42}\approx6.481$, both above $5.117$. For $B$ itself, $\det(B-\lambda I)=(1-\lambda)(4-\lambda)+6=\lambda^2-5\lambda+10$. The roots are $(5\pm i\sqrt{15})/2$, whose magnitudes are $\sqrt{25/4+15/4}=\sqrt{10}\approx3.162$. Thus $\rho(B)=\sqrt{10}\le\|B\|_2$. The symmetric spectral theorem was used for $B^\top B$; $B$ is nonsymmetric and its eigenvalue magnitudes need not equal its singular values.</p>
''')
replace('::exercise-31', 'Connects each Cholesky equation to the symbolic pivot, verifies leading minors and the singular boundary, and shows every triangular solve.', r'''
<p><strong>(a) Match a lower triangular factor.</strong> Start with $P(a)=LL^\top$ and positive diagonal pivots. Entry $(1,1)$ gives $\ell_{11}=1$; entries $(2,1)$ and $(3,1)$ then give $\ell_{21}=2$ and $\ell_{31}=0$. Entry $(2,2)$ gives $\ell_{22}^2=5-2^2=1$, so $\ell_{22}=1$. Entry $(3,2)$ gives $\ell_{31}\ell_{21}+\ell_{32}\ell_{22}=2$, hence $\ell_{32}=2$. Finally $\ell_{33}^2=a-0^2-2^2=a-4$. All pivots are positive exactly when $a\gt4$, proving positive definiteness in that range.</p>
<p><strong>(b) Check leading minors.</strong> The first two are $1$ and $1\cdot5-2\cdot2=1$. Expansion along the first row gives $\det P(a)=(5a-4)-2(2a)=a-4$. Sylvester's criterion for a real symmetric matrix therefore gives the same condition $a\gt4$.</p>
<p><strong>(c) Check the boundary directly.</strong> At $a=4$ the factor $L=\begin{bmatrix}1&0&0\\2&1&0\\0&2&0\end{bmatrix}$ still satisfies $P(4)=LL^\top$. Thus $z^\top P(4)z=\|L^\top z\|_2^2\ge0$. For $z=(4,-2,1)$, $L^\top z=(4-4,-2+2,0)=(0,0,0)$, so this nonzero vector is in the nullspace. The matrix is PSD but singular. If $a\lt4$, the same vector gives quadratic value $a-4\lt0$ and disproves PSD.</p>
<p><strong>(d) Solve for $a=5$.</strong> Now $\ell_{33}=1$. In $Ly=(1,4,5)^\top$, the rows give $y_1=1$, $2y_1+y_2=4$ so $y_2=2$, and $2y_2+y_3=5$ so $y_3=1$. Backward substitution in $L^\top x=y$ gives $x_3=1$, $x_2+2x_3=2$ so $x_2=0$, and $x_1+2x_2=1$ so $x_1=1$. Direct multiplication confirms $P(5)(1,0,1)^\top=(1,4,5)^\top$. All three diagonal pivots are $1$, so $\det P(5)=(1\cdot1\cdot1)^2=1$ and $\log\det P(5)=0$.</p>
''')
replace('::exercise-32', 'Explains eigen-coordinates and farthest-point equality, derives the shadow by minimizing over the second coordinate, and verifies the symmetric square root.', r'''
<p><strong>(a) Read the axes in an orthonormal eigenbasis.</strong> Multiplication gives $P(1,-1)^\top=9(1,-1)^\top$ and $P(1,1)^\top=(1,1)^\top$. Normalize to $q_1=(1,-1)/\sqrt2$ and $q_2=(1,1)/\sqrt2$. Writing $x=\xi_1q_1+\xi_2q_2$ turns the constraint into $9\xi_1^2+\xi_2^2\le1$, or $\xi_1^2/(1/3)^2+\xi_2^2/1^2\le1$. Thus the semi-axes are $1/3$ and $1$, and the area is $\pi(1/3)(1)=\pi/3$.</p>
<p><strong>(b) Find the farthest points.</strong> Orthonormality gives $\|x\|_2^2=\xi_1^2+\xi_2^2\le9\xi_1^2+\xi_2^2\le1$. Equality requires $\xi_1=0$ and $\xi_2^2=1$, so the farthest points are $\pm q_2$, both at distance $1$.</p>
<p><strong>(c) Distinguish the shadow from the slice.</strong> For a fixed $x_1$, the shadow allows any $x_2$ satisfying the constraint. Complete the square:</p>
<div class="math-block">$$5x_1^2-8x_1x_2+5x_2^2=5(x_2-4x_1/5)^2+\frac95x_1^2.$$</div>
<p>The minimum over $x_2$ occurs at $x_2=4x_1/5$, so a feasible $x_2$ exists exactly when $(9/5)x_1^2\le1$. The shadow half-width is $\sqrt5/3\approx0.745356$. In the slice $x_2=0$, the condition instead is $5x_1^2\le1$, giving half-width $1/\sqrt5\approx0.447214$. The ellipse's tilt lets its shadow extend beyond that slice.</p>
<p><strong>(d) Test the point.</strong> At $(0.5,0.5)$ the quadratic value is $5(0.25)-8(0.25)+5(0.25)=1.25-2+1.25=0.5\le1$, so the point is inside.</p>
<p><strong>(e) Construct the symmetric map from a ball.</strong> Scale the $q_1$ direction by $1/3$ and the $q_2$ direction by $1$. This gives</p>
<div class="math-block">$$R=\frac13q_1q_1^\top+q_2q_2^\top=\frac13\begin{bmatrix}2&1\\1&2\end{bmatrix},\qquad R^2=\frac19\begin{bmatrix}5&4\\4&5\end{bmatrix}=P^{-1}.$$</div>
<p>In the same eigenbasis, $RPR=I$, so $x=Ru$ has $x^\top Px=\|u\|_2^2$. Conversely $R$ is invertible and $u=R^{-1}x$ has this same equality. Both directions prove $\mathcal E=\{Ru:\|u\|_2\le1\}$, rather than only showing inclusion.</p>
''')
replace('::exercise-33', 'Supplies a complete SVD, exact pseudoinverse projection, and an elementary proof of both the range and scalar Schur conditions.', r'''
<p><strong>(a) Factor the rank-one matrix.</strong> Let $u=(1,2)/\sqrt5$ and $v=(-2,1)/\sqrt5$. They are perpendicular unit vectors, and $C=5uu^\top$. Thus an SVD is $U=V=[u\ v]$, $\Sigma=\operatorname{diag}(5,0)$. Exactly one singular value is nonzero, so the rank is $1$. Invert the nonzero singular value and leave the zero one at zero: $C^+=(1/5)uu^\top=C/25$.</p>
<p><strong>(b) Compute and check the residual.</strong> For $b=(1,0)$, $x=C^+b=(1,2)/25$. Then $Cx=(1/5,2/5)$ and $b-Cx=(4/5,-2/5)$. The range of $C$ is the line spanned by $(1,2)$, and the residual's dot product with that direction is $4/5+2(-2/5)=0$. Therefore the residual is perpendicular to the whole range.</p>
<p><strong>(c) Decide range membership.</strong> If $(1,0)=q(1,2)$, the first coordinate forces $q=1$ while the second forces $q=0$, a contradiction. Hence $b$ is not in the range, consistent with the nonzero residual.</p>
<p><strong>(d) Prove the range condition before taking a Schur complement.</strong> Write a vector for the block form as $(t,z)$, with $z\in\mathbb R^2$. Its value is $at^2+2t\beta^\top z+z^\top Cz$. The null vector $n=(2,-1)$ satisfies $Cn=0$. Taking $t=1$ and $z=sn$ leaves $a+2s\beta^\top n$. If $\beta^\top n\ne0$, choosing $s$ with a large opposite sign makes this negative. PSD therefore requires $2\beta_1-\beta_2=0$, or $\beta=q(1,2)$.</p>
<p>Under that condition let $h=z_1+2z_2$. Then $z^\top Cz=h^2$ and $\beta^\top z=qh$, so the block form becomes</p>
<div class="math-block">$$at^2+2qth+h^2=(h+qt)^2+(a-q^2)t^2.$$</div>
<p>It is nonnegative for all $t,z$ when $a\ge q^2$. Conversely, $t=1$ and any $z$ with $h=-q$ make the first square zero, so PSD requires $a\ge q^2$. Hence the exact answer is $\beta=q(1,2)$ and $a\ge q^2$. This also agrees with $C^+\beta=(q/5,2q/5)$ and $\beta^\top C^+\beta=q^2$. For the forbidden choice $\beta=(1,0)$, the test vector $(1,s(2,-1))$ gives $a+4s$, negative whenever $s\lt-a/4$, no matter how $a$ is chosen.</p>
''')
replace('::exercise-34', 'Shows all numerical determinant and variance substitutions and explains their equality with a finite Gram Schur complement, without an unnecessary finite-feature assumption.', r'''
<p><strong>(a) Compute the determinant directly.</strong> Dividing each kernel entry by $\lambda=1/2$ and adding the identity gives $I+K/\lambda=\begin{bmatrix}3&1\\1&3\end{bmatrix}$. Its determinant is $3\cdot3-1\cdot1=8$.</p>
<p><strong>(b) Add the observations sequentially.</strong> The first factor is $1+k(x_1,x_1)/\lambda=1+1/(1/2)=3$. Before observing the second point, its variance is</p>
<div class="math-block">$$\sigma_1^2(x_2)=1-\frac{(1/2)^2}{1+1/2}=1-\frac{1/4}{3/2}=1-\frac16=\frac56.$$</div>
<p>The second factor is $1+(5/6)/(1/2)=1+5/3=8/3$. Multiplying gives $3(8/3)=8$, the same determinant.</p>
<p><strong>(c) Take the logarithm.</strong> The quantity is $(1/2)\log8\approx1.03972$ nats. The unit is nats because the logarithm is natural; bits would require base two.</p>
<p><strong>(d) Explain why the two computations agree.</strong> Write $a=k(x_1,x_1)+\lambda$ and $b=k(x_2,x_1)$. The determinant of $K+\lambda I$ factors as $a[k(x_2,x_2)+\lambda-b^2/a]=a[\lambda+\sigma_1^2(x_2)]$. Since $I+K/\lambda=(K+\lambda I)/\lambda$ is two-dimensional, its determinant divides this expression by $\lambda^2$. The result is precisely $(1+k(x_1,x_1)/\lambda)(1+\sigma_1^2(x_2)/\lambda)$. In larger finite Gram matrices, block elimination applies the same Schur-complement factor at each added observation, so the determinant ratios telescope into the sequential product. Positive $\lambda$ keeps these elimination blocks invertible.</p>
''')
replace('::exercise-35', 'Derives the similarity, PSD threshold and equality direction, and states explicitly that this is a gain in the M input metric.', r'''
<p><strong>(a) Compute the eigenvalues and explain their sign.</strong> Here $W^\top W=\begin{bmatrix}1&1\\1&1\end{bmatrix}$ and $M^{-1}=\operatorname{diag}(1,1/2)$, so $A=W^\top WM^{-1}=\begin{bmatrix}1&1/2\\1&1/2\end{bmatrix}$ is not symmetric. Its trace is $3/2$ and determinant is zero; the characteristic polynomial is $\lambda^2-(3/2)\lambda=\lambda(\lambda-3/2)$. Thus its eigenvalues are $0$ and $3/2$.</p>
<p>For a structural explanation, put $g=M^{-1/2}W^\top=(1,1/\sqrt2)^\top$. Then $S=M^{-1/2}W^\top WM^{-1/2}=gg^\top$ is symmetric PSD, and $A=M^{1/2}SM^{-1/2}$ is similar to $S$. Similar matrices have the same eigenvalues; $gg^\top$ has eigenvalue $\|g\|_2^2=3/2$ along $g$ and zero perpendicular to $g$.</p>
<p><strong>(b) Find the largest feasible $F$.</strong> Congruence by the invertible $M^{-1/2}$ preserves PSD and turns $M-FW^\top W$ into $I-Fgg^\top$. Its eigenvalues are $1-(3/2)F$ and $1$, so for $F\ge0$ it is PSD exactly when $F\le2/3$. The largest feasible value is $F=2/3$. Directly,</p>
<div class="math-block">$$M-FW^\top W=\begin{bmatrix}1-F&-F\\-F&2-F\end{bmatrix},\qquad\det= (1-F)(2-F)-F^2=2-3F.$$</div>
<p>For $0\le F\le2/3$ both diagonal entries are nonnegative and the determinant is nonnegative, satisfying the symmetric $2$ by $2$ PSD test. At $F=2/3$ the diagonal entries are $1/3$ and $4/3$ and the determinant is zero. Above it the negative determinant rules out PSD.</p>
<p><strong>(c) Find where the ratio is maximal.</strong> The ratio is defined for $x\ne0$. Set $u=M^{1/2}x$, so $x^\top Mx=\|u\|_2^2$ and $Wx=g^\top u$. Cauchy–Schwarz gives $(g^\top u)^2/\|u\|_2^2\le\|g\|_2^2=3/2$. Equality holds precisely when $u$ is a nonzero multiple of $g$, hence when $x$ is a nonzero multiple of $M^{-1}W^\top=(1,1/2)^\top$. At that vector the numerator is $(3/2)^2=9/4$ and denominator is $1+2(1/2)^2=3/2$, giving ratio $3/2$.</p>
<p>The reciprocal optimum $1/F=3/2$ is the squared gain from the input norm $\|x\|_M=\sqrt{x^\top Mx}$ to the scalar output norm, giving gain $\sqrt{3/2}$. The ordinary Euclidean norm of this row is instead $\sqrt2$. Reporting the input metric is essential when using this generalized-eigenvalue step in the <a href="lipsdp.html#scalability">Module 12 layer-wise calculation</a>.</p>
''')

retained = {
'la-ex-norms-1':'Explicit coordinate products, absolute values and squares, perpendicularity criterion and numerical comparison already cover every requested calculation.',
'la-ex-norms-2':'Each feasible set has a proved upper bound and a checked attaining vector; the existing interpretation explains the differing maxima.',
'la-ex-matrix-norms-1':'Displays both row and column sums, the Frobenius sum of squares, and an explicit input attaining the induced 1-norm bound.',
'la-ex-matrix-norms-2':'Computes the diagonal product entrywise, verifies its stretch on every input and explains why the separate worst directions do not compose.',
'la-ex-spectral-1':'Verifies both eigen-equations, normalization and orthogonality and reconstructs the matrix from the outer products.',
'la-ex-spectral-2':'Shows the matrix-vector product, quadratic form and quotient, checks both numerical eigenvalue bounds and identifies every equality direction.',
'la-ex-spectral-3':'Computes the characteristic polynomial and negative quadratic form, then derives why only the symmetric part controls that form and states the failed assumption.',
'la-ex-psd-1':'Computes a form for all vectors for the singular PSD case and gives explicit positive and negative witnesses for the indefinite case.',
'la-ex-svd-1':'Provides actual orthogonal factors, squared singular values, norm and condition calculations and the reflection/ellipse interpretation.',
'la-ex-svd-2':'Computes the pseudoinverse and all solutions, then proves uniqueness of minimum norm by orthogonal decomposition into a sum of squares.',
'la-ex-svd-3':'Shows both normalized iterates and norm estimates, calculates the failed scaling certificate and explains two guaranteed alternatives.',
'la-ex-blocks-1':'Works each row product and diagonal trace, then computes and explains the block determinant product.',
'la-ex-structured-1':'Checks the orthogonal identity and length preservation, evaluates the specified vector and uses determinant and fixed axis to identify reflection.',
'la-ex-structured-2':'Shows the image, symmetry and idempotence, computes the residual and orthogonality, and distinguishes a singular projection from an orthogonal matrix.',
'la-ex-functions-1':'Evaluates each integral, solves the scalar orthogonality equation and verifies the projection norm decomposition.',
'la-ex-functions-2':'Computes the Gram entries and expands its form as a sum of squares, then proves its vanishing set is only the zero vector.',
'la-ex-functions-3':'Solves both interpolation conditions, checks both norm coordinates and the representer, and explains the unbounded domain with a contrasting bounded-domain estimate.',
}

rows=[]
for ex in baseline['exercises']:
    key='::exercise-'+str(ex['ordinal']) if ex['anchor'] is None else ex['anchor']
    if key not in replacements and key not in retained:
        raise ValueError('Unreviewed exercise '+ex['inventory_key'])
    row={'inventory_key':ex['inventory_key'],'source_file':ex['source_file'],
         'original_solution_sha256':ex['solution']['sha256'],
         'decision':'replace' if key in replacements else 'retain',
         'thoroughness_rationale':reasons.get(key,retained.get(key))}
    if key in replacements:
        row['replacement_html']=replacements[key]
    rows.append(row)
result={'status':'authored_all35_pending_independent_semantic_review',
        'reader_baseline':'First-course linear algebra and single-variable calculus.',
        'baseline_sha256':hashlib.sha256((ROOT/'book/solutions/baseline-source90/pages/primer-linalg.html.json').read_bytes()).hexdigest(),
        'exercises':rows}
out=ROOT/'book/solutions/drafts/primer-linalg-thorough-solutions-v1.json'
data=(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode()
if out.exists() and out.read_bytes()!=data:
    raise RuntimeError('Refusing to overwrite a different draft')
out.write_bytes(data)
print(json.dumps({'draft':str(out.relative_to(ROOT)),'exercises':len(rows),'replaced':len(replacements),'retained':len(retained),'sha256':hashlib.sha256(data).hexdigest()}))
