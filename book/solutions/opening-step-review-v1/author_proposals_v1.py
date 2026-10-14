"""Exercise-specific opening proposals, authored against exact current Source91.

Only records under this directory/reports/solution-review may be created.
Reader pages, authored chapters, the old tracker and Git remain untouched.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review

BASE = 'book/solutions/opening-step-review-v1'
SNAPSHOT = review.read(BASE + '/current-source-v1.json')
DECISIONS = {}


def replace(page, ordinal, rationale, body):
    key = (page + '.html', ordinal)
    assert key not in DECISIONS
    DECISIONS[key] = {'decision': 'replace', 'thoroughness_rationale': rationale,
                      'replacement_html': body.strip() + '\n'}


def retain(page, ordinal, rationale):
    key = (page + '.html', ordinal)
    assert key not in DECISIONS
    DECISIONS[key] = {'decision': 'retain', 'thoroughness_rationale': rationale}


replace('primer-basics', 1,
    'Replace the compressed square list with the set-builder filtering rule and an explicit signed multiplication/comparison for every permitted input; distinguish the membership test from the universal subset test and exhibit its failing element.',
    r"""
<p>A set-builder expression is a filter. For $A$, start with the six numbers in $X$ and keep a number precisely when its square is at most $4$. Squaring means multiplying the number by itself; a negative number times a negative number is positive.</p>
<table><thead><tr><th>Input $x$</th><th>Square</th><th>Keep in $A$?</th></tr></thead><tbody>
<tr><td>$-2$</td><td>$(-2)(-2)=4$</td><td>Yes: $4\le4$.</td></tr>
<tr><td>$-1$</td><td>$(-1)(-1)=1$</td><td>Yes: $1\le4$.</td></tr>
<tr><td>$0$</td><td>$0(0)=0$</td><td>Yes: $0\le4$.</td></tr>
<tr><td>$1$</td><td>$1(1)=1$</td><td>Yes: $1\le4$.</td></tr>
<tr><td>$2$</td><td>$2(2)=4$</td><td>Yes: $4\le4$.</td></tr>
<tr><td>$3$</td><td>$3(3)=9$</td><td>No: $9\gt4$.</td></tr>
</tbody></table>
<p>Therefore $A=\{-2,-1,0,1,2\}$. Equality is allowed by $\le$, so both $-2$ and $2$ stay.</p>
<p>For $B$, use the different test $x\gt0$. The negative numbers $-2,-1$ fail, and $0$ fails because it is equal to zero, not greater. The numbers $1,2,3$ pass. Hence $B=\{1,2,3\}$.</p>
<p>The membership statement $2\in A$ asks about one number. It is true: $2$ is in $X$ and $2^2=4\le4$. The subset statement $B\subseteq A$ asks whether <em>every</em> member of $B$ belongs to $A$. Checking $1$ and $2$ succeeds, but $3\in B$ and $3\notin A$. That one counterexample proves $B\not\subseteq A$.</p>
""")

replace('primer-basics', 2,
    'The results are correct, but a first set-operation exercise benefits from checking all six universe elements against the four different logical tests, including the role of equality/universe rather than merely presenting the resulting sets.',
    r"""
<p>Use the membership rule for each operation: union means “in $A$ or in $B$”; intersection means “in both”; difference means “in $A$ and outside $B$”; complement means “in the stated universe $X$ and outside $A$”.</p>
<p><strong>Union.</strong> Start with $A=\{0,2,4\}$. From $B=\{2,3,4\}$, the elements $2,4$ are already present, while $3$ is new. A set lists an element only once. Thus $A\cup B=\{0,2,3,4\}$. Neither $1$ nor $5$ is in either set, so neither is added.</p>
<p><strong>Intersection.</strong> Test the three members of $A$: $0$ is not in $B$, but $2$ and $4$ are. These are all the possible common members, so $A\cap B=\{2,4\}$.</p>
<p><strong>Difference.</strong> Begin with $A$ again, and remove its members that are also in $B$. Remove $2$ and $4$; keep $0$. Therefore $A\setminus B=\{0\}$. The element $3$ cannot appear in this difference because it was never in $A$.</p>
<p><strong>Complement.</strong> Begin with all of $X=\{0,1,2,3,4,5\}$, and remove $0,2,4$, the members of $A$. What remains is $A^c=X\setminus A=\{1,3,5\}$. Numbers outside $X$, such as $6$, are not in this complement: the universe is part of its definition.</p>
""")

replace('primer-basics', 3,
    'Spell out why every real square is nonnegative through sign cases, then apply universal/existential definitions separately; make the dependent witness and fixed-witness contradiction explicit instead of relying on short truth labels.',
    r"""
<p><strong>(1) Every real square is nonnegative: true.</strong> Take any real $x$. If $x=0$, then $x^2=0$. If $x\gt0$, the product $x\cdot x$ is positive. If $x\lt0$, write $x=-a$ with $a\gt0$; then $x^2=(-a)(-a)=a^2\gt0$. These cases cover every real number, so $x^2\ge0$ for every $x\in\mathbb R$.</p>
<p><strong>(2) Some real square equals $-1$: false.</strong> An existential claim needs at least one permitted input. Part (1) says every permitted square is at least $0$, whereas $-1\lt0$. Thus no real input can satisfy $x^2=-1$.</p>
<p><strong>(3) For every $x$ there is a $y$ with $y=x+2$: true.</strong> First take an arbitrary real $x$. We may now choose $y=x+2$. A real number plus $2$ is real, so the chosen $y$ lies in the required domain. Substituting that choice into the equation gives $x+2=x+2$, which is true. The choice may depend on the $x$ we were given.</p>
<p><strong>(4) One $y$ works for every $x$: false.</strong> Suppose someone fixes a real $y$ first. The phrase “every real $x$” includes the choice $x=y$. For that input, the required equation becomes $y=y+2$. Subtract $y$ from both sides to obtain $0=2$, a contradiction. Hence no proposed fixed $y$ works. The distinction is the order of the choices: a separate answer to each input can exist even though one shared answer does not.</p>
""")

replace('primer-basics', 4,
    'Show the two quantifier swaps in the second statement individually and explain each negated comparison, then verify in-domain witnesses and the included equality boundary.',
    r"""
<p><strong>(1) Negate $\forall x\in\mathbb R:\ x^2\ge1$.</strong> A universal statement fails when at least one allowed input fails its test. Replace “for every” by “there exists”, and negate $x^2\ge1$ to $x^2\lt1$:</p>
<div class="math-block">$$\neg(\forall x\in\mathbb R:\ x^2\ge1)
\quad\Longleftrightarrow\quad
\exists x\in\mathbb R:\ x^2\lt1.$$</div>
<p>Choose $x=0$, which is a real number. Its square is $0\cdot0=0$, and $0\lt1$. The negation is true, so the original statement is false.</p>
<p><strong>(2) Negate $\exists x\in[0,1]\ \forall y\in[0,1]:x\gt y$.</strong> The outer “there exists $x$” becomes “for every $x$”. For each such $x$, the inner “for every $y$” becomes “there exists $y$”. Finally, “$x$ is greater than $y$” fails when $x$ is less than or equal to $y$. Therefore the full negation is</p>
<div class="math-block">$$\forall x\in[0,1]\ \exists y\in[0,1]:\ x\le y.$$</div>
<p>To prove it, take any allowed $x$ and choose $y=x$. The choice is in $[0,1]$ because $x$ is, and $x\le x$ holds with equality. Thus the negation is true and the original is false. In the original, the same choice $y=x$ directly breaks the strict condition $x\gt y$. No endpoint exception is possible: this works at $x=0$, at $x=1$, and between them. The domains stay unchanged throughout.</p>
""")

replace('primer-basics', 5,
    'Add the missing positive-factor proof for squaring an inequality, the square-root/absolute-value bridge for the contrapositive, explicit logical negations, and both sufficient/necessary interpretations; the converse counterexample alone is not the whole assessment.',
    r"""
<p><strong>Original implication.</strong> Here $P$ means $x\gt3$ and $Q$ means $x^2\gt9$. To test $P\Rightarrow Q$, assume $x\gt3$. Then $x-3\gt0$, and adding $3$ gives $x+3\gt6\gt0$. The product of these two positive factors is positive:</p>
<div class="math-block">$$x^2-9=(x-3)(x+3)\gt0.$$</div>
<p>Adding $9$ yields $x^2\gt9$. This proves the implication for every input satisfying its premise. For an input with $x\le3$, the implication makes no promise that $Q$ must be false.</p>
<p><strong>Converse.</strong> Reverse the arrow: $x^2\gt9\Rightarrow x\gt3$. At $x=-4$, the square is $(-4)(-4)=16\gt9$, so the premise is true. But $-4\lt3$, so the conclusion is false. An implication fails at any input with a true premise and a false conclusion; therefore this converse is false.</p>
<p><strong>Contrapositive.</strong> Negate each statement and reverse their order. The negation of $Q$ is $x^2\le9$; the negation of $P$ is $x\le3$. Thus the contrapositive is $x^2\le9\Rightarrow x\le3$. The square-root function preserves order between nonnegative numbers, giving $\sqrt{x^2}\le\sqrt9$, or $|x|\le3$. If $x\ge0$, this means $x\le3$. If $x\lt0$, then already $x\lt0\lt3$; also $|x|=-x\le3$ gives $x\ge-3$ after multiplying by $-1$ and reversing the inequality. Hence the premise implies $-3\le x\le3$, and in particular $x\le3$. The contrapositive is true, as equivalence with the original implication predicts.</p>
<p><strong>Necessary and sufficient.</strong> $P$ is sufficient for $Q$: knowing $P$ guarantees $Q$. Equivalently, $Q$ is necessary for $P$: every input with $P$ must also have $Q$. But $P$ is not necessary for $Q$, because the input $-4$ has $Q$ without $P$. Equivalently, $Q$ is not sufficient for $P$. A necessary condition need not guarantee the conclusion on its own.</p>
""")

replace('primer-basics', 6,
    'Explain the definitions of infinite union/intersection, both inclusions for the union, and the integer-choice/positive reciprocal steps that exclude an arbitrary nonzero point, including why choosing a strict inequality matters.',
    r"""
<p><strong>Union: membership in at least one interval.</strong> At $k=1$, $A_1=[-1,1]$. For every integer $k\ge1$, the positive reciprocal satisfies $0\lt1/k\le1$. Thus any $x\in A_k$ satisfies</p>
<div class="math-block">$$-1\le-1/k\le x\le1/k\le1.$$</div>
<p>Every interval is contained in $[-1,1]$, so the union has no points outside that interval. Conversely, every point of $[-1,1]$ is already in $A_1$, hence in the union. These two inclusions prove $\bigcup_{k\ge1}A_k=[-1,1]$.</p>
<p><strong>Intersection: membership in every interval.</strong> For every $k\ge1$, $-1/k\le0\le1/k$, so $0$ belongs to every $A_k$ and therefore to their intersection.</p>
<p>Now take any $x\ne0$. Its absolute value is positive, so $1/|x|$ is a finite positive number. Integers have no finite upper bound; choose an integer $k\gt1/|x|$. Multiply by the positive number $|x|$, then divide by the positive integer $k$:</p>
<div class="math-block">$$k\gt\frac1{|x|}
\quad\Longrightarrow\quad k|x|\gt1
\quad\Longrightarrow\quad |x|\gt\frac1k.$$</div>
<p>A point belongs to $[-1/k,1/k]$ exactly when $|x|\le1/k$. Our strict opposite inequality shows $x\notin A_k$. Intersection membership requires every test to pass, so this one failed test excludes $x$. No nonzero real point remains, and $\bigcap_{k\ge1}A_k=\{0\}$. The intersection is not empty: all intervals still share their centre.</p>
""")

replace('primer-basics', 7,
    'Make the arbitrary-element set equality proof readable as individual membership/and/not/or rules, with the middle and endpoint cases spelled out instead of presenting an unexplained equivalence chain.',
    r"""
<p>Membership in $A$ requires $x\ge-1$, while membership in $B$ requires $x\le2$. Membership in the intersection requires both tests. Hence</p>
<div class="math-block">$$A\cap B=\{x\in\mathbb R:-1\le x\le2\}=[-1,2].$$</div>
<p>The complement is taken in $\mathbb R$. A real point outside $[-1,2]$ is either less than $-1$ or greater than $2$. Therefore $(A\cap B)^c=(-\infty,-1)\cup(2,\infty)$. Both endpoints are excluded: $-1$ and $2$ pass both original non-strict tests.</p>
<p>For the equality proof, take an arbitrary real $x$. Apply the definitions one at a time:</p>
<div class="math-block">$$\begin{aligned}
x\in(A\cap B)^c
&\iff x\notin A\cap B\\
&\iff \neg(x\in A\ \wedge\ x\in B)\\
&\iff (x\notin A)\ \vee\ (x\notin B)\\
&\iff (x\in A^c)\ \vee\ (x\in B^c)\\
&\iff x\in A^c\cup B^c.
\end{aligned}$$</div>
<p>The middle step says that “both tests pass” fails precisely when at least one fails. Here failure of $x\ge-1$ means $x\lt-1$, and failure of $x\le2$ means $x\gt2$. A point in the middle interval fails neither condition; a point to the left fails the first, and one to the right fails the second. Thus $A^c=(-\infty,-1)$ and $B^c=(2,\infty)$, giving the same complement. The equivalences hold for every real $x$ and in both directions, so the sets have exactly the same members and are equal.</p>
""")

replace('primer-basics', 8,
    'Expose the finite state/input case analysis and quantify the negation explicitly; explain why a witness may depend on state and why failure of both shared commands is distinct from a state with no safe command.',
    r"""
<p>Read the safe-pair list before changing any quantifiers. At state $a$, the list contains $(a,L)$ and not $(a,R)$, so the safe inputs are $\{L\}$. At $b$, only $(b,R)$ occurs, giving $\{R\}$. At $c$, both pairs occur, giving $\{L,R\}$.</p>
<p><strong>(1) One permitted choice for each state: true.</strong> “For every $x$ there exists $u$” allows us to see the state before choosing the input. Choose $L$ at $a$, $R$ at $b$, and $L$ at $c$. The corresponding pairs $(a,L),(b,R),(c,L)$ are all explicitly in $S$. These choices cover all three states, so the universal statement is proved.</p>
<p><strong>(2) One input shared by all states: false.</strong> There are only two candidate shared inputs. If we fix $L$, the test at $b$ fails because $(b,L)\notin S$. If we fix $R$, the test at $a$ fails because $(a,R)\notin S$. Every candidate is ruled out. Equivalently, the common safe-input set is $\{L\}\cap\{R\}\cap\{L,R\}=\emptyset$.</p>
<p><strong>Negation of (1).</strong> Swap the outer universal quantifier for an existential one, swap the inner existential quantifier for a universal one, and negate membership:</p>
<div class="math-block">$$\exists x\in X\ \forall u\in U:\ (x,u)\notin S.$$</div>
<p>This says that some state has no safe input at all. It is false: $a$ has the safe choice $L$, $b$ has $R$, and $c$ has both. At each proposed state, that permitted choice disproves “every input fails”. There can therefore be a safe response at every state while there is no single safe input for all states.</p>
""")

replace('primer-basics', 9,
    'Show the unique cancellation input, the interval inequalities and sign reversal in necessity/sufficiency, exact a=1 boundary and a=0 failure, and the contradictory endpoint requirements for a shared input.',
    r"""
<p>First solve the cancellation equation for its only possible input. Subtracting $x$ from $x+u=0$ gives $u=-x$. We must check whether this required input lies in $[-a,a]$; solving the equation alone does not establish admissibility.</p>
<p><strong>A separate cancelling input for every state.</strong> For necessity, use the allowed boundary state $x=1$. Its only cancelling input is $u=-1$. Membership in $[-a,a]$ requires both $-a\le-1$ and $-1\le a$. The second holds automatically for $a\ge0$. Multiplying the first inequality by $-1$ reverses its direction and gives $a\ge1$. Thus the quantified claim cannot hold when $a\lt1$.</p>
<p>For sufficiency, assume $a\ge1$ and take any $-1\le x\le1$. Multiply the two bounds by $-1$, reversing their order, to obtain $-1\le-x\le1$. Choose $u=-x$. Because $a\ge1$, we have $-a\le-1$ and $1\le a$, so</p>
<div class="math-block">$$-a\le-1\le u\le1\le a.$$</div>
<p>This proves $u\in U$, and substitution gives $x+u=x+(-x)=0$. It works for every allowed state. Hence the exact range is $a\in[1,\infty)$. Equality $a=1$ works, including $x=\pm1$; at $a=0$ only input $0$ is allowed, which cannot cancel $x=1$.</p>
<p><strong>One fixed input for all states.</strong> If such an input existed, the allowed state $x=1$ would force $1+u=0$, hence $u=-1$. The other allowed state $x=-1$ would force $-1+u=0$, hence $u=1$. A single real number cannot equal both $-1$ and $1$. Thus no $a\ge0$, however large, makes this stronger statement true. Increasing the input interval can provide more state-dependent choices; it cannot make the uniquely required values equal.</p>
""")

replace('primer-basics', 10,
    'Distinguish declared domain/codomain from attained outputs, show each signed square individually, and connect duplicate/unreachable outputs to the definitions of injectivity and surjectivity.',
    r"""
<p>In the declaration $f:X\to Y$, the <em>domain</em> is the set of permitted inputs $X=\{-2,-1,0,1,2\}$, and the <em>codomain</em> is the declared target $Y=\{0,1,4,9\}$. These sets are part of the question, rather than something to infer from the formula alone.</p>
<p>The image is the set of outputs actually obtained from the permitted inputs. Evaluate them all:</p>
<div class="math-block">$$\begin{aligned}
f(-2)&=(-2)(-2)=4,& f(-1)&=(-1)(-1)=1,\\
f(0)&=0(0)=0,& f(1)&=1(1)=1,\\
f(2)&=2(2)=4.
\end{aligned}$$</div>
<p>Repeated outputs are listed only once in a set. Thus $f(X)=\{0,1,4\}$. The codomain permits $9$, but this calculation shows that $9$ is never reached.</p>
<p>Injectivity would mean that equal outputs come only from equal inputs. Here $-1\ne1$, yet $f(-1)=f(1)=1$, so the map is not injective.</p>
<p>Surjectivity onto $Y$ would mean that every member of $Y$ has a preimage in $X$. The value $9\in Y$ has no such input, as the exhaustive five-input list shows. Inputs $\pm3$ would give $9$, but neither is in $X$, so they cannot repair the claim. The map is not surjective onto its stated codomain.</p>
""")

replace('primer-basics', 11,
    'Expand the nested function substitutions, arithmetic and binomial products instead of skipping directly between intermediate outputs; use the unequal values at the same input to justify noncommutation.',
    r"""
<p>The definition $(f\circ g)(x)=f(g(x))$ tells us to apply the function on the right first. For $f\circ g$ at $2$, compute</p>
<div class="math-block">$$g(2)=2^2=2\cdot2=4,\qquad
f(4)=2\cdot4-1=8-1=7.$$</div>
<p>Therefore $(f\circ g)(2)=7$. In the opposite order, compute</p>
<div class="math-block">$$f(2)=2\cdot2-1=4-1=3,\qquad
g(3)=3^2=3\cdot3=9.$$</div>
<p>Therefore $(g\circ f)(2)=9$.</p>
<p>For a general real input, substitute the whole output of the inner function into the formula of the outer one:</p>
<div class="math-block">$$\begin{aligned}
(f\circ g)(x)&=f(x^2)=2x^2-1,\\
(g\circ f)(x)&=g(2x-1)=(2x-1)^2\\
&=(2x-1)(2x-1)\\
&=4x^2-2x-2x+1\\
&=4x^2-4x+1.
\end{aligned}$$</div>
<p>The two middle products are each $-2x$, which is why the combined linear term is $-4x$. Both compositions are defined for every real $x$. Their values $7$ and $9$ at the same input $2$ differ, so they cannot be the same function. Composition order matters.</p>
""")

replace('primer-basics', 12,
    'Show the fixed-point rearrangement and substitution check, every common-denominator/reciprocal step in the three iterates, and the algebra connecting signed error to the distance-reduction factor.',
    r"""
<p>A fixed point is an input that comes back unchanged. Set $(x^\ast+3)/4=x^\ast$. Multiply both sides by $4$, subtract $x^\ast$, then divide by $3$:</p>
<div class="math-block">$$x^\ast+3=4x^\ast
\quad\Longrightarrow\quad3=3x^\ast
\quad\Longrightarrow\quad x^\ast=1.$$</div>
<p>Checking the answer gives $g(1)=(1+3)/4=4/4=1$.</p>
<p>In the iteration, use each new output as the next input. Write integers with the needed denominator before adding fractions:</p>
<div class="math-block">$$\begin{aligned}
x_1&=\frac{-1+3}{4}=\frac2{4}=\frac12,\\
x_2&=\frac{1/2+3}{4}
=\frac{1/2+6/2}{4}
=\frac{7/2}{4}=\frac78,\\
x_3&=\frac{7/8+3}{4}
=\frac{7/8+24/8}{4}
=\frac{31/8}{4}=\frac{31}{32}.
\end{aligned}$$</div>
<p>Dividing a fraction by $4$ multiplies its denominator by $4$. The distances from the fixed point are $|x_0-1|=|-2|=2$, $|x_1-1|=|1/2-2/2|=1/2$, $|x_2-1|=|7/8-8/8|=1/8$, and $|x_3-1|=|31/32-32/32|=1/32$.</p>
<p>The pattern holds at every step, not just these three. Subtract the fixed point using a common denominator:</p>
<div class="math-block">$$g(x)-1=\frac{x+3}{4}-\frac44
=\frac{x-1}{4},\qquad
|g(x)-1|=\frac14|x-1|.$$</div>
<p>Thus each update divides the distance by $4$. Starting from distance $2$, the exact distance after $k$ steps is $2(1/4)^k$, which tends to zero.</p>
""")

# REMAINING_ASSESSMENTS
