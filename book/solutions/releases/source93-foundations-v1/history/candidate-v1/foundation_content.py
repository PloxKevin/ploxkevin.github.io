"""Authored guided practice for Primer 0; all mathematics is reviewed separately.

Each row is an actual problem, hint and worked argument, not a template used to
manufacture solution depth. The release helper inserts these in local practice.
"""

EXERCISES = []


def add(group, code, level, title, question, hint, solution):
    EXERCISES.append(dict(group=group, code=code, level=level, title=title,
                          question=question.strip(), hint=hint.strip(),
                          solution=solution.strip()))


add('warmup', 'W1', 'Easy', 'Keep the sign and the brackets',
r'''<p>Calculate $(-3)^2$, $-3^2$, $(-2)^3$, $|-2-3|$, and $|2-(-3)|$. Write the multiplication or subtraction before giving the answer. Explain which two expressions measure a distance.</p>''',
r'''<p>A power acts on its bracketed base. Without brackets, the power is evaluated before a leading minus. Distance is the absolute value of the difference between two positions.</p>''',
r'''<p><strong>Step 1: Identify the base of each power.</strong> In $(-3)^2$, the base is the whole number $-3$. Squaring it means multiplying two copies:</p>
<div class="math-block">$$(-3)^2=(-3)(-3)=9.$$</div>
<p>The product of two negative numbers is positive. In $-3^2$, the base of the power is $3$; the leading minus is applied afterwards. Thus $-3^2=-(3\cdot3)=-9$. The brackets change the order of operations, so these two expressions have different values.</p>
<p><strong>Step 2: Expand the odd power.</strong> Three copies of $-2$ give $(-2)^3=(-2)(-2)(-2)$. Multiply the first two to obtain $4$, then multiply $4$ by $-2$ to obtain $-8$. An odd number of negative factors leaves a negative product.</p>
<p><strong>Step 3: Perform subtraction before taking absolute value.</strong> First, $-2-3=-5$, so $|-2-3|=|-5|=5$. Second, subtracting a negative adds its positive opposite: $2-(-3)=2+3=5$, so $|2-(-3)|=|5|=5$. Absolute value measures how far a number lies from zero; that distance cannot be negative.</p>
<p><strong>Step 4: Interpret the two distances.</strong> $|-2-3|$ is the distance between positions $-2$ and $3$, and $|2-(-3)|$ is the distance between $2$ and $-3$. Each interval has length $5$. Swapping the two positions changes the sign of their difference but preserves its absolute value. This is the scalar distance used in later error and contraction bounds.</p>''')

add('warmup', 'W2', 'Easy', 'Add fractions and divide by a fraction',
r'''<p>Calculate $1/4+2/3$, $(1/2+3)/4$, and $2/(1/2)$. Then solve $x/3+1/2=5/6$ and check your answer in the original equation. Show common denominators explicitly.</p>''',
r'''<p>Adding fractions requires equal denominators. Dividing by a nonzero number multiplies by its reciprocal. Apply the same operation to both sides of the equation.</p>''',
r'''<p><strong>Step 1: Put the first two fractions over a common denominator.</strong> A denominator divisible by both $4$ and $3$ is $12$. Multiplying a fraction's numerator and denominator by the same nonzero number preserves its value:</p>
<div class="math-block">$$\frac14+\frac23=\frac3{12}+\frac8{12}=\frac{11}{12}.$$</div>
<p>We add numerators because each now counts twelfths. Adding the denominators would change the size of the pieces and would not perform the required addition.</p>
<p><strong>Step 2: Complete the bracket before dividing.</strong> Write $3=6/2$. Then $(1/2+3)/4=(7/2)/4=(7/2)(1/4)=7/8$. Division by $4$ multiplies by $1/4$; it does not divide both numerator and denominator by $4$.</p>
<p><strong>Step 3: Divide by a fraction.</strong> The reciprocal of $1/2$ is $2$, since $(1/2)2=1$. Therefore $2/(1/2)=2\cdot2=4$. As a check, four halves fit into two whole units, and $4(1/2)=2$.</p>
<p><strong>Step 4: Isolate the unknown.</strong> Subtract $1/2=3/6$ from both sides of $x/3+1/2=5/6$. This leaves $x/3=5/6-3/6=2/6=1/3$. Multiply both sides by $3$ to get $x=1$.</p>
<p><strong>Step 5: Check the original equation.</strong> Substitution gives $1/3+1/2=2/6+3/6=5/6$, as required. Checking the original form can catch an arithmetic mistake introduced while rearranging. The same common-denominator steps will appear when we calculate fixed-point iterates.</p>''')

add('warmup', 'W3', 'Easy', 'Read powers and a finite sum',
r'''<p>Calculate $2^{-3}$ and $(1/2)^0$. Expand $\sum_{t=0}^{3}(1/2)^t$ into individual terms and add them. How many terms are there? Explain why $\sum_{t=1}^{3}(1/2)^t$ has a different value.</p>''',
r'''<p>A negative exponent takes a reciprocal. A sum includes both its starting and ending indices; the index is a placeholder replaced by each integer in that range.</p>''',
r'''<p><strong>Step 1: Translate the exponent rules into arithmetic.</strong> $2^{-3}=1/2^3=1/(2\cdot2\cdot2)=1/8$. For a nonzero base, the zeroth power is $1$, so $(1/2)^0=1$. These are two different rules: a negative power takes a reciprocal, whereas a zeroth power supplies the starting unit.</p>
<p><strong>Step 2: List the indices before evaluating.</strong> In $\sum_{t=0}^{3}(1/2)^t$, the symbol $t$ takes values $0,1,2,3$. The upper index is included. There are $3-0+1=4$ terms:</p>
<div class="math-block">$$\sum_{t=0}^{3}(1/2)^t=1+\frac12+\frac14+\frac18.$$</div>
<p><strong>Step 3: Add with one denominator.</strong> Writing all four terms in eighths gives $(8+4+2+1)/8=15/8=1.875$. The sum is less than $2$; we will later show that the infinite sum is exactly $2$.</p>
<p><strong>Step 4: Change the starting index carefully.</strong> The second sum uses only $t=1,2,3$. Its value is $1/2+1/4+1/8=(4+2+1)/8=7/8$. It is smaller than the first sum by the omitted $t=0$ term, which is $1$. A horizon of $T$ terms starting at time $0$ therefore ends at time $T-1$, not time $T$.</p>''')

add('warmup', 'W4', 'Easy', 'Solve an inequality without losing its direction',
r'''<p>Solve $-3x+2\le8$ over the reals and write the answer as an interval. Then solve $1\le2x+3\lt7$. Check an endpoint, an interior point and an excluded point for each answer.</p>''',
r'''<p>Subtracting the same number preserves order. Dividing by a negative number reverses order. A double inequality imposes two conditions at once.</p>''',
r'''<p><strong>Step 1: Remove the constant term.</strong> Subtract $2$ from both sides of $-3x+2\le8$, obtaining $-3x\le6$.</p>
<p><strong>Step 2: Divide by the coefficient and account for its sign.</strong> The coefficient $-3$ is negative. Division reverses the inequality, so $x\ge6/(-3)=-2$. The complete solution set is $[-2,\infty)$. Its left endpoint is included because the original comparison allows equality; infinity is never an included real endpoint.</p>
<p><strong>Step 3: Verify three inputs.</strong> At $x=-2$, the original left side is $6+2=8$, so the endpoint works. At $x=0$, it is $2\le8$, so this interior point works. At $x=-3$, it is $9+2=11\gt8$, so this excluded point fails. Had we kept the wrong direction when dividing, these checks would reveal it.</p>
<p><strong>Step 4: Solve both sides of the double inequality.</strong> Subtract $3$ from all three expressions to obtain $-2\le2x\lt4$. Divide by the positive number $2$, preserving both directions: $-1\le x\lt2$. The solution interval is $[-1,2)$.</p>
<p><strong>Step 5: Check both endpoint types.</strong> At $x=-1$, $2x+3=1$, so the non-strict lower condition holds. At $x=0$, the value is $3$, between $1$ and $7$. At $x=2$, the value is $7$, so the strict upper condition fails. The different brackets record different requirements.</p>''')

add('warmup', 'W5', 'Medium', 'Turn an absolute-value test into an interval',
r'''<p>Solve $|x-2|\le3$ and $x^2\le4$ over $\mathbb R$. Compare the latter with $x^2\lt4$. Show why taking a square root must keep both possible signs of $x$.</p>''',
r'''<p>For $r\ge0$, $|z|\le r$ means $-r\le z\le r$. Also $\sqrt{x^2}=|x|$ on the whole real line.</p>''',
r'''<p><strong>Step 1: Read the distance condition.</strong> $|x-2|\le3$ says that $x$ is at most $3$ units from the centre $2$. Equivalently, $-3\le x-2\le3$. Adding $2$ to all three parts gives $-1\le x\le5$. Thus the answer is $[-1,5]$. Both endpoints have distance $3$ from the centre and are allowed.</p>
<p><strong>Step 2: Take square roots between nonnegative quantities.</strong> The square-root function preserves their order, so $x^2\le4$ is equivalent to $\sqrt{x^2}\le\sqrt4$, or $|x|\le2$. It is not equivalent just to $x\le2$: that would incorrectly permit $x=-3$, whose square is $9$.</p>
<p><strong>Step 3: Resolve the absolute value.</strong> If $x\ge0$, $|x|=x$, giving $0\le x\le2$. If $x\lt0$, $|x|=-x$, giving $-x\le2$, hence $x\ge-2$ after reversing the inequality when multiplying by $-1$. Combining the two branches gives $[-2,2]$.</p>
<p><strong>Step 4: Track strictness.</strong> For $x^2\lt4$ the same argument gives $|x|\lt2$, hence $-2\lt x\lt2$. The answer is now $(-2,2)$. At $x=\pm2$, the square is exactly $4$, so those endpoints pass the non-strict question and fail the strict one. At $x=0$, both questions pass. This distinction later changes whether an iteration budget meets an error tolerance.</p>''')

add('warmup', 'W6', 'Medium', 'Solve a power bound and round the iteration count',
r'''<p>Find the smallest integer $k\ge0$ such that $3(1/2)^k\le0.1$. First solve for a real $k$ using logarithms, then check neighbouring integer powers. How does the reasoning change when you divide an inequality by $\log(1/2)$?</p>''',
r'''<p>Natural logarithms increase on positive numbers, but $\log(1/2)$ is negative. An integer budget must be rounded up after solving a lower bound on $k$.</p>''',
r'''<p><strong>Step 1: Isolate the exponential.</strong> Divide the original inequality by $3\gt0$ to get $(1/2)^k\le1/30$. Both sides are positive, so applying the increasing natural logarithm preserves the direction:</p>
<div class="math-block">$$k\log(1/2)\le\log(1/30).$$</div>
<p><strong>Step 2: Check the sign before dividing.</strong> Since $0\lt1/2\lt1$, its logarithm is negative. Dividing reverses the inequality, giving $k\ge\log(1/30)/\log(1/2)=\log30/\log2\approx4.907$. The two minus signs cancel in the ratio; they do not remove the need to reverse the comparison.</p>
<p><strong>Step 3: Choose an integer.</strong> The least integer at least $4.907$ is $5$, denoted $\lceil4.907\rceil$. Rounding to the nearest integer is not the general rule: a budget must satisfy the derived inequality.</p>
<p><strong>Step 4: Verify without rounded logarithms.</strong> At $k=4$, the error expression is $3/16=0.1875\gt0.1$. At $k=5$, it is $3/32=0.09375\lt0.1$. Every increase in $k$ divides it by $2$, so all earlier integers also fail and all later ones pass. This establishes the smallest budget exactly, even though the logarithm calculation was approximate.</p>''')

add('sets', 'GS1', 'Easy', 'Separate an element from a set of elements',
r'''<p>Let $A=\{1,2\}$ and $B=\{\{1\},2\}$. Decide whether $1\in A$, $\{1\}\subseteq A$, $\{1\}\in A$, $\{1\}\in B$, and $\emptyset\subseteq A$. Find $|A|$ and $|B|$. Explain each test in words.</p>''',
r'''<p>Membership tests one listed object. A subset test examines the elements inside the proposed subset. The number $1$ and the set $\{1\}$ are different objects.</p>''',
r'''<p><strong>Step 1: List the objects in each set.</strong> $A$ contains the numbers $1$ and $2$. $B$ contains the singleton set $\{1\}$ as one object and the number $2$ as another. Braces create a set; they are part of the object being described.</p>
<p><strong>Step 2: Test membership.</strong> $1\in A$ is true because the number $1$ is listed. $\{1\}\in A$ is false because the singleton set is not either listed number. $\{1\}\in B$ is true because that singleton set is explicitly one of $B$'s two objects.</p>
<p><strong>Step 3: Test a subset.</strong> $\{1\}\subseteq A$ means that every member of $\{1\}$ belongs to $A$. Its only member is the number $1$, and $1\in A$, so this statement is true. It does not ask whether the singleton itself is listed in $A$.</p>
<p><strong>Step 4: Handle the empty set.</strong> $\emptyset\subseteq A$ means that every element of the empty set belongs to $A$. There is no element that could fail this test. Formally, a failure would require an $x\in\emptyset$ with $x\notin A$, and such an $x$ does not exist. The subset statement is therefore true; this is called a vacuously true universal statement.</p>
<p><strong>Step 5: Count distinct elements.</strong> Both $|A|$ and $|B|$ are $2$. The singleton in $B$ counts as one element of $B$; we do not open it and count its contents again. Vertical bars around a finite set mean cardinality, whereas vertical bars around a real number mean absolute value. The type of the object determines which meaning applies.</p>''')

add('sets', 'GS2', 'Easy', 'Build a Cartesian product and read its pairs',
r'''<p>For $X=\{a,b\}$ and $U=\{L,R\}$, list $X\times U$. Let $S=\{(a,L),(b,L),(b,R)\}$. Find the allowed inputs at each state, a rule choosing one allowed input per state, and every input allowed at both states. Compare $(a,L)$ with $(L,a)$.</p>''',
r'''<p>A product independently chooses one element of each set. Fixing the first coordinate gives one row of the safe-pair list.</p>''',
r'''<p><strong>Step 1: Enumerate independent choices.</strong> Pair $a$ with each input to obtain $(a,L),(a,R)$. Pair $b$ with each input to obtain $(b,L),(b,R)$. Thus</p>
<div class="math-block">$$X\times U=\{(a,L),(a,R),(b,L),(b,R)\}.$$</div>
<p>There are $|X||U|=2\cdot2=4$ pairs. The two choices form a product, rather than a sum of possibilities.</p>
<p><strong>Step 2: Filter the product with $S$.</strong> At state $a$, only $(a,L)$ is listed in $S$, so the allowed-input set is $U(a)=\{L\}$. At $b$, both listed pairs are allowed, so $U(b)=\{L,R\}$.</p>
<p><strong>Step 3: Choose a response after seeing the state.</strong> One rule is $\pi(a)=L$, $\pi(b)=R$. Each selected pair lies in $S$, so this rule satisfies “every state has an allowed input”. Choosing $L$ at both states would also be a valid rule; the question asks for one rule, not a unique rule.</p>
<p><strong>Step 4: Require a shared input.</strong> A shared input must lie in the intersection $U(a)\cap U(b)=\{L\}\cap\{L,R\}=\{L\}$. Hence $L$ works at both states and $R$ fails at $a$. In this particular example, both quantifier orders succeed; they need not do so for every safe-pair list.</p>
<p><strong>Step 5: Keep the coordinate roles.</strong> $(a,L)$ is an ordered pair with a state first and an input second. $(L,a)$ reverses these roles and is not a member of $X\times U$, since $L\notin X$ and $a\notin U$. Ordered pairs cannot be rearranged like the elements inside a set.</p>''')

add('sets', 'GS3', 'Easy', 'Read an implication with a truth table',
r'''<p>Let $P$ mean “$x\gt2$” and $Q$ mean “$x\gt0$”, for real $x$. At $x=3,1,-1$, assess $P$, $Q$, and $P\Rightarrow Q$. Complete the four-row truth table for an abstract implication. Which row refutes an implication?</p>''',
r'''<p>“If $P$, then $Q$” rules out a true premise with a false conclusion. A false premise does not demand that the conclusion be false.</p>''',
r'''<p><strong>Step 1: Translate the promise.</strong> $P\Rightarrow Q$ promises that whenever $P$ holds, $Q$ holds too. It does not promise the reverse, and it says nothing about the value of $Q$ when $P$ fails.</p>
<table><thead><tr><th>$P$</th><th>$Q$</th><th>$P\Rightarrow Q$</th></tr></thead><tbody>
<tr><td>True</td><td>True</td><td>True: the promise is met.</td></tr>
<tr><td>True</td><td>False</td><td>False: the promise is broken.</td></tr>
<tr><td>False</td><td>True</td><td>True: its premise was not met.</td></tr>
<tr><td>False</td><td>False</td><td>True: its premise was not met.</td></tr>
</tbody></table>
<p><strong>Step 2: Substitute the three specified inputs.</strong> At $x=3$, both $3\gt2$ and $3\gt0$ are true, so the implication is true. At $x=1$, $1\gt2$ is false while $1\gt0$ is true, giving the third row. At $x=-1$, both comparisons are false, giving the fourth row. The implication is true at all three inputs.</p>
<p><strong>Step 3: Prove the statement beyond those examples.</strong> If an arbitrary real $x$ satisfies $x\gt2$, transitivity with $2\gt0$ gives $x\gt0$. Thus no real input produces the failing second row, and the implication holds for every real $x$.</p>
<p><strong>Step 4: Identify a counterexample correctly.</strong> An example with $P$ false cannot refute the implication. To refute its converse $Q\Rightarrow P$, use $x=1$: this makes $Q$ true and $P$ false. Counterexamples must check the premise and the conclusion separately.</p>''')

add('sets', 'GS4', 'Medium', 'Unpack a robust statement one choice at a time',
r'''<p>Let $X=[-1,1]$, $U=[-1,1]$, and $W=[-1/4,1/4]$. Prove $\forall x\in X\ \exists u\in U\ \forall w\in W:\ |x+u+w|\le1/4$. Write its negation and explain which variables a chosen $u$ may depend on.</p>''',
r'''<p>Choose a command that cancels the observed state. Then keep that command fixed while testing every disturbance. Negating a non-strict bound makes it strict.</p>''',
r'''<p><strong>Step 1: Read the quantifiers from left to right.</strong> First an arbitrary $x\in[-1,1]$ is given. We must now supply one $u\in[-1,1]$. Only after that choice is fixed must the test pass for every $w\in[-1/4,1/4]$. The command can depend on $x$ but cannot depend on the later disturbance.</p>
<p><strong>Step 2: Construct and check the command.</strong> Set $u=-x$. From $-1\le x\le1$, multiplying by $-1$ gives $-1\le-x\le1$, so $u$ is allowed. This domain check is part of proving an existential claim.</p>
<p><strong>Step 3: Prove the final universal condition.</strong> Keep $u=-x$ and take any permitted $w$. Then $x+u+w=x-x+w=w$. Its interval bounds imply $|w|\le1/4$, so $|x+u+w|\le1/4$. The endpoints $w=\pm1/4$ give equality and are allowed. Because no extra restriction was imposed on $x$ or $w$, the complete statement is proved.</p>
<p><strong>Step 4: Negate every layer.</strong> Swap each universal quantifier with an existential one, and each existential quantifier with a universal one, without changing the domains. The negation is</p>
<div class="math-block">$$\exists x\in X\ \forall u\in U\ \exists w\in W:\ |x+u+w|\gt1/4.$$</div>
<p>In words, some allowed state would defeat every legal command, with an allowed disturbance showing the failure of each command. It is false here: for any proposed state, the command $-x$ already passes all disturbances. A disturbance used to refute a command may depend on that command, because its existential quantifier comes afterwards.</p>''')

add('functions', 'GF1', 'Easy', 'Evaluate a formula and check where it is defined',
r'''<p>Let $f(x)=(2x+1)/(x-1)$ with real inputs. Find its largest real domain, calculate $f(0)$ and $f(2)$, and explain why $f(1)$ is undefined. Solve $f(x)=3$ and check whether the solution belongs to the domain.</p>''',
r'''<p>Division by zero is undefined. When solving the equation, retain that restriction even after multiplying by the denominator.</p>''',
r'''<p><strong>Step 1: Determine the allowed inputs.</strong> The numerator $2x+1$ is defined for every real $x$. The denominator vanishes exactly when $x-1=0$, or $x=1$. Thus the largest real domain is $\mathbb R\setminus\{1\}$. Declaring the codomain to be $\mathbb R$ is valid because every defined quotient is real.</p>
<p><strong>Step 2: Substitute into the whole fraction.</strong> At $x=0$, the numerator is $2(0)+1=1$ and the denominator is $0-1=-1$, so $f(0)=-1$. At $x=2$, they are $2(2)+1=5$ and $2-1=1$, so $f(2)=5$. At $x=1$, the numerator is $3$ and the denominator is $0$. A quotient $3/0$ cannot be a real number: any proposed value $q$ would have to satisfy $0q=3$, which is impossible.</p>
<p><strong>Step 3: Solve for a specified output.</strong> Require $(2x+1)/(x-1)=3$ with $x\ne1$. Multiplying both sides by the nonzero denominator gives $2x+1=3(x-1)=3x-3$. Subtract $2x$ and add $3$ to obtain $x=4$.</p>
<p><strong>Step 4: Check the domain and the original equation.</strong> The candidate $4$ is not $1$, so it is allowed. Substitution gives $f(4)=(8+1)/(4-1)=9/3=3$. We have found the preimage of the output $3$. Multiplying an equation by a nonzero quantity preserves equality regardless of its sign; unlike an inequality, an equation has no direction to reverse.</p>''')

add('functions', 'GF2', 'Easy', 'Keep the direction of an image or preimage',
r'''<p>For $f:\mathbb R\to\mathbb R$, $f(x)=2x-1$, find $f([0,2])$ and $f^{-1}([0,2])$. Find an inverse formula and verify both compositions. Explain why the same interval appears on different sides of the two calculations.</p>''',
r'''<p>An image starts with an input restriction. A preimage starts with an output restriction and solves that condition for the inputs.</p>''',
r'''<p><strong>Step 1: Push the input interval through the formula.</strong> For $0\le x\le2$, multiply by $2\gt0$ and subtract $1$ to obtain $-1\le2x-1\le3$. This proves that the image is contained in $[-1,3]$.</p>
<p><strong>Step 2: Show that every proposed output is reached.</strong> Take any $y\in[-1,3]$ and choose $x=(y+1)/2$. The output bounds give $0\le(y+1)/2\le2$, so the chosen input lies in $[0,2]$. Substituting it gives $f(x)=2((y+1)/2)-1=y$. Both inclusions now prove $f([0,2])=[-1,3]$.</p>
<p><strong>Step 3: Pull the required output interval back to the inputs.</strong> The preimage question asks for all real $x$ such that $0\le f(x)\le2$. Substitute the formula, add $1$, then divide by $2$:</p>
<div class="math-block">$$0\le2x-1\le2\iff1\le2x\le3\iff\tfrac12\le x\le\tfrac32.$$</div>
<p>Hence $f^{-1}([0,2])=[1/2,3/2]$. These are inputs; the interval $[0,2]$ in this question specified outputs.</p>
<p><strong>Step 4: Verify an inverse function.</strong> Define $q(y)=(y+1)/2$ on $\mathbb R$. Then $f(q(y))=y$, as above, and $q(f(x))=((2x-1)+1)/2=x$. These two identities verify that $q=f^{-1}$. Preimage notation also makes sense for maps without an inverse; in this example an inverse exists because every real output has exactly one input.</p>''')

add('functions', 'GF3', 'Easy', 'Read a safe set as a level-set inequality',
r'''<p>Let $h(x)=4-x^2$ and $C=\{x\in\mathbb R:h(x)\ge0\}$. Find $C$, the zero set $\{x:h(x)=0\}$, and the strict set $\{x:h(x)\gt0\}$. Check $x=-2,0,3$. Is $h$ itself a set?</p>''',
r'''<p>First evaluate the function. A level set collects inputs passing a comparison on that output. Rearrange the comparison before solving it.</p>''',
r'''<p><strong>Step 1: Separate the function from the set.</strong> $h$ is a rule assigning the real output $4-x^2$ to an input $x$. $C$ is a collection of inputs. The braces and comparison turn that function into a membership test; the function itself is not that collection.</p>
<p><strong>Step 2: Solve the non-strict test.</strong> The condition $h(x)\ge0$ means $4-x^2\ge0$. Adding $x^2$ to both sides gives $x^2\le4$. By the absolute-value calculation, this is equivalent to $|x|\le2$, or $-2\le x\le2$. Thus $C=[-2,2]$.</p>
<p><strong>Step 3: Find the other level sets.</strong> For the zero set, $4-x^2=0$ gives $x^2=4$, so both $x=-2$ and $x=2$ qualify. It is the set $\{-2,2\}$. For the strict set, $4-x^2\gt0$ gives $x^2\lt4$, hence $(-2,2)$. Its endpoints are excluded.</p>
<p><strong>Step 4: Check actual values.</strong> $h(-2)=4-4=0$, so $-2$ is safe under the non-strict rule and lies in the zero set. $h(0)=4$, so $0$ lies in both the non-strict and strict sets. $h(3)=4-9=-5$, so $3$ lies in neither. The number $4=h(0)$ is an output value; it is not a safe input here, since $h(4)=-12$. Keeping the input and output roles separate prevents this confusion.</p>''')

add('functions', 'GF4', 'Medium', 'Compute a set of admissible commands',
r'''<p>For a known real state $x$, define $U(x)=\{u\in[-1,1]:0\le x+u\le2\}$. Derive an interval formula, evaluate it at $x=0,1,2,3,4$, and find exactly which states have at least one admissible command. Explain why $U$ is a set-valued map.</p>''',
r'''<p>Subtract $x$ from the two safety bounds, then intersect with the actuator interval. An interval is empty if its lower endpoint exceeds its upper endpoint.</p>''',
r'''<p><strong>Step 1: Solve the safety condition for the command.</strong> For a fixed observed $x$, subtracting $x$ gives $-x\le u\le2-x$. Safety alone permits $[-x,2-x]$, but the actuator permits only $[-1,1]$.</p>
<p><strong>Step 2: Combine both restrictions.</strong> The lower endpoint must meet both lower bounds, hence is their maximum. The upper endpoint must meet both upper bounds, hence is their minimum:</p>
<div class="math-block">$$U(x)=[-1,1]\cap[-x,2-x].$$</div>
<p>Equivalently, its endpoints are $\ell(x)=\max\{-1,-x\}$ and $r(x)=\min\{1,2-x\}$ when $\ell(x)\le r(x)$. If $\ell(x)\gt r(x)$, the set is empty. We must check that comparison rather than treating a reversed interval as nonempty.</p>
<p><strong>Step 3: Evaluate the five states.</strong> At $0$, the intersection is $[-1,1]\cap[0,2]=[0,1]$. At $1$, it is $[-1,1]$. At $2$, it is $[-1,1]\cap[-2,0]=[-1,0]$. At $3$, it is $[-1,1]\cap[-3,-1]=\{-1\}$. At $4$, it is $[-1,1]\cap[-4,-2]=\emptyset$.</p>
<p><strong>Step 4: Find the complete feasibility range.</strong> Two closed intervals intersect exactly when each lower endpoint is at most the other's upper endpoint. Here the nontrivial conditions are $-1\le2-x$, giving $x\le3$, and $-x\le1$, giving $x\ge-1$. Thus a command exists exactly for $x\in[-1,3]$. At the left boundary, $u=1$ yields successor $0$; at the right boundary, $u=-1$ yields successor $2$. Outside this range, even an extreme actuator command cannot reach $[0,2]$.</p>
<p><strong>Step 5: Interpret the map.</strong> Each input state is assigned a set of commands, which can contain many values, one value or none. A controller selects one member when the set is nonempty. This differs from an ordinary real-valued function, which assigns a single real output to each input in its domain.</p>''')

add('proofs', 'GP1', 'Easy', 'Prove both directions of an equivalence',
r'''<p>Prove, for real $x$, that $x\ge2$ if and only if $3x+1\ge7$. Write one argument for each direction, and explain which direction would be enough to prove only that $x\ge2$ is sufficient.</p>''',
r'''<p>An “if and only if” claim contains two implications. In each direction, assume its starting condition and derive the other condition.</p>''',
r'''<p><strong>Step 1: Name the two statements.</strong> Let $P$ be $x\ge2$ and $Q$ be $3x+1\ge7$. To prove $P\iff Q$, we need both $P\Rightarrow Q$ and $Q\Rightarrow P$.</p>
<p><strong>Step 2: Prove the forward implication.</strong> Assume $x\ge2$. Multiplying by $3\gt0$ preserves order and gives $3x\ge6$. Adding $1$ gives $3x+1\ge7$. This proves $P\Rightarrow Q$: the starting condition is sufficient.</p>
<p><strong>Step 3: Prove the reverse implication.</strong> Assume instead $3x+1\ge7$. Subtracting $1$ gives $3x\ge6$. Dividing by $3\gt0$ preserves order and gives $x\ge2$. This proves $Q\Rightarrow P$: the starting condition in the first direction is also necessary.</p>
<p><strong>Step 4: Conclude precisely.</strong> Both implications hold for every real $x$, so the equivalence is proved. At $x=2$, both sides allow equality. A check at that endpoint confirms the bracket choice but cannot replace the two general implications. If the request were only sufficiency, Step 2 would suffice; Step 3 is what establishes necessity.</p>''')

add('proofs', 'GP2', 'Easy', 'Construct the integer your proof needs',
r'''<p>Prove that the sum of two even integers is even. Then prove that the sum of two odd integers is even. In each case give the integer that witnesses the definition of evenness; checking a few examples is not enough.</p>''',
r'''<p>“Even” means equal to $2q$ for some integer $q$. Replace each starting integer by its defining form and factor out $2$.</p>''',
r'''<p><strong>Step 1: Write the hypothesis using the definition.</strong> Let $a,b$ be arbitrary even integers. There are integers $m,n$ such that $a=2m$ and $b=2n$. These two integers may differ; evenness does not require a shared witness.</p>
<p><strong>Step 2: Calculate the sum and supply a witness.</strong> $a+b=2m+2n=2(m+n)$. The number $q=m+n$ is an integer because integers are closed under addition. Therefore $a+b=2q$ for an integer $q$, exactly the definition of an even number. This proves the first claim for every allowed pair, including negative numbers and zero.</p>
<p><strong>Step 3: Repeat with the correct odd forms.</strong> If $a,b$ are odd, write $a=2m+1$ and $b=2n+1$ for integers $m,n$. Then</p>
<div class="math-block">$$a+b=2m+1+2n+1=2m+2n+2=2(m+n+1).$$</div>
<p>Now the witness is $q=m+n+1$, also an integer. Thus the sum is even. Merely saying that the final expression “looks even” would omit the domain check on $q$.</p>
<p><strong>Step 4: Compare a check with a proof.</strong> $(-3)+5=2$ checks one odd pair. The symbolic calculation covers every odd pair because $m,n$ were arbitrary. A finite list of successful examples cannot prove a statement about all integers; a definition-based witness can.</p>''')

add('proofs', 'GP3', 'Medium', 'Use induction to prove an inequality',
r'''<p>Prove $2^n\ge n+1$ for every integer $n\ge0$. State the induction hypothesis and identify where $n\ge0$ is used in the step. Check $n=0,1,2$ separately to understand the claim before proving it.</p>''',
r'''<p>At the next index, $2^{n+1}=2\cdot2^n$. Use the hypothesis to bound this below, then compare the resulting expression with $n+2$.</p>''',
r'''<p><strong>Step 1: Read a few instances.</strong> At $n=0$, $2^0=1=0+1$. At $n=1$, $2^1=2=1+1$. At $n=2$, $2^2=4\ge3$. Equality at the first two indices is permitted by the non-strict comparison.</p>
<p><strong>Step 2: Establish the base case.</strong> Define $P(n)$ to mean $2^n\ge n+1$. The $n=0$ calculation proves $P(0)$.</p>
<p><strong>Step 3: State what may be assumed.</strong> Fix an integer $n\ge0$ and assume $P(n)$, namely $2^n\ge n+1$. The target is $P(n+1)$, namely $2^{n+1}\ge(n+1)+1=n+2$. We do not assume this target.</p>
<p><strong>Step 4: Derive the next bound.</strong> The power rule and positive multiplication give $2^{n+1}=2\cdot2^n\ge2(n+1)=2n+2$. To compare with $n+2$, subtract: $(2n+2)-(n+2)=n\ge0$. Hence $2n+2\ge n+2$, so $2^{n+1}\ge n+2$. This is the desired next statement.</p>
<p><strong>Step 5: Apply induction.</strong> The base case and the implication $P(n)\Rightarrow P(n+1)$ prove the inequality for every integer $n\ge0$. The nonnegativity of $n$ was needed in comparing the two linear expressions; it was not an unstated assumption about the size of $2^n$.</p>''')

add('proofs', 'GP4', 'Medium', 'Combine error bounds with the triangle inequality',
r'''<p>A true scalar value $x$, a sensor reading $y$ and a prediction $z$ satisfy $|x-y|\le0.2$ and $|y-z|\le0.1$. Prove $|x-z|\le0.3$. If $z=4.7$, can these bounds certify $x\in[0,5]$? Is the bound $0.3$ attainable?</p>''',
r'''<p>Insert the intermediate value: $x-z=(x-y)+(y-z)$. To certify an interval, check the extreme compatible values, including equality.</p>''',
r'''<p><strong>Step 1: Decompose the unknown difference.</strong> Adding and subtracting $y$ changes nothing: $x-z=x-y+y-z=(x-y)+(y-z)$. This lets us connect a quantity we want to bound to the two quantities we know.</p>
<p><strong>Step 2: Apply the triangle inequality.</strong> For real $a,b$, $|a+b|\le|a|+|b|$. Use $a=x-y$, $b=y-z$, then substitute the two hypotheses:</p>
<div class="math-block">$$|x-z|\le|x-y|+|y-z|\le0.2+0.1=0.3.$$</div>
<p>We did not assume the errors have the same sign or cancel; the bound must cover either possibility.</p>
<p><strong>Step 3: Turn the bound into an information interval.</strong> If $z=4.7$, then $-0.3\le x-4.7\le0.3$. Adding $4.7$ gives $4.4\le x\le5.0$. The whole interval $[4.4,5]$ lies in $[0,5]$, so these assumptions certify the specification. At the upper endpoint, equality $x=5$ is allowed.</p>
<p><strong>Step 4: Check whether the bound could be improved from this information.</strong> Choose $z=4.7$, $y=4.8$, $x=5.0$. Then $|x-y|=0.2$, $|y-z|=0.1$, and $|x-z|=0.3$. All hypotheses hold with both signed errors pointing the same way, so the combined bound is attained. A smaller universal error bound would exclude this allowed example. Cancellation might improve a particular reading, but it cannot be guaranteed from these two absolute bounds alone.</p>''')

add('sequences', 'GL1', 'Easy', 'Build an epsilon proof from a tolerance calculation',
r'''<p>For $a_t=1/(t+1)$, $t=0,1,2,\dots$, calculate the first four terms and prove $a_t\to0$ from the definition of convergence. For any given $\varepsilon\gt0$, supply an explicit integer $T$ such that $|a_t|\lt\varepsilon$ for every $t\ge T$. Check your rule for $\varepsilon=1/4$.</p>''',
r'''<p>Choose $T$ after seeing the tolerance. $\lfloor r\rfloor$ is the greatest integer at most $r$, so $\lfloor r\rfloor+1\gt r$.</p>''',
r'''<p><strong>Step 1: Evaluate the indices.</strong> Substitution gives $a_0=1$, $a_1=1/2$, $a_2=1/3$, $a_3=1/4$. The candidate limit is $0$, so its distance from $a_t$ is $|a_t-0|=1/(t+1)$.</p>
<p><strong>Step 2: State the target in the correct order.</strong> Convergence to $0$ means that for every real tolerance $\varepsilon\gt0$, there is an integer $T\ge0$ such that every integer $t\ge T$ satisfies $|a_t|\lt\varepsilon$. $T$ may depend on the tolerance, but it must cover all later indices at once.</p>
<p><strong>Step 3: Choose a definite integer.</strong> Given $\varepsilon\gt0$, set $T=\lfloor1/\varepsilon\rfloor+1$. It is a nonnegative integer and $T\gt1/\varepsilon$. For any $t\ge T$, the denominator satisfies $t+1\ge T+1\gt1/\varepsilon$. Taking reciprocals of positive numbers reverses order, yielding $1/(t+1)\lt\varepsilon$.</p>
<p><strong>Step 4: Conclude for every tolerance.</strong> We gave a legal $T$ and verified the requested inequality for every later $t$, so the definition proves $a_t\to0$. The rule is sufficient; the definition does not require the smallest possible $T$.</p>
<p><strong>Step 5: Test the distinction.</strong> At $\varepsilon=1/4$, our rule gives $T=5$, and $a_t\le1/6\lt1/4$ for all $t\ge5$. The smallest threshold is actually $4$: $a_4=1/5\lt1/4$, whereas $a_3=1/4$ fails the strict test. A sufficient convergence witness can be larger than a minimal computational budget.</p>''')

add('sequences', 'GL2', 'Easy', 'Separate terms, partial sums and a tail',
r'''<p>Let $a_t=(1/2)^t$ and $S_T=\sum_{t=0}^{T-1}a_t$, with $S_0=0$. Calculate $S_1,S_2,S_3,S_4$. Derive $S_T=2(1-2^{-T})$ and the omitted infinite tail $2^{1-T}$. Explain why $a_t\to0$ is a different statement from $S_T\to2$.</p>''',
r'''<p>Multiply a finite sum by $1/2$ and subtract; intermediate terms cancel. A tail starts at the first index you have not included.</p>''',
r'''<p><strong>Step 1: Track how many terms are included.</strong> $S_1=1$. $S_2=1+1/2=3/2$. $S_3=3/2+1/4=7/4$. $S_4=7/4+1/8=15/8$. The subscript $T$ counts terms; the last included term is $a_{T-1}$.</p>
<p><strong>Step 2: Derive the finite formula before taking a limit.</strong> For $T\ge1$, write $S_T=1+1/2+\cdots+2^{-(T-1)}$ and $(1/2)S_T=1/2+1/4+\cdots+2^{-T}$. Subtracting cancels all shared terms:</p>
<div class="math-block">$$S_T-\tfrac12S_T=1-2^{-T}.$$</div>
<p>Thus $(1/2)S_T=1-2^{-T}$, and multiplying by $2$ gives $S_T=2(1-2^{-T})$. It also holds at $T=0$, since $2(1-1)=0=S_0$.</p>
<p><strong>Step 3: Define the infinite sum through its partial sums.</strong> Because $2^{-T}\to0$, the finite-sum formula gives $S_T\to2$. This limit is what we mean by $\sum_{t=0}^{\infty}a_t=2$.</p>
<p><strong>Step 4: Subtract the included portion.</strong> The omitted tail after $T$ terms is $2-S_T=2-2(1-2^{-T})=2\cdot2^{-T}=2^{1-T}$. At $T=4$, it is $2-15/8=1/8$; its first term is $a_4=1/16$, and the remaining terms supply the other $1/16$.</p>
<p><strong>Step 5: Distinguish two sequences.</strong> $a_t$ is one term at a time, and its limit is zero. $S_T$ is the accumulation of the first $T$ terms, and its limit is two. Terms tending to zero is necessary for a series to converge, but is not sufficient: $1/(t+1)$ tends to zero while its harmonic series diverges. The geometric calculation establishes convergence here rather than assuming it from the term limit.</p>''')

add('sequences', 'GL3', 'Medium', 'Watch a telescoping sum cancel',
r'''<p>Define $b_t=1/(t+1)-1/(t+2)$ for $t\ge0$. Calculate $b_0,b_1,b_2$ and expand $\sum_{t=0}^{2}b_t$ before simplifying. Derive the $T$-term partial sum and the infinite sum. Can all the terms be positive while the sum stays finite?</p>''',
r'''<p>The second fraction of one term cancels the first fraction of the next. Keep the first and last uncancelled fractions.</p>''',
r'''<p><strong>Step 1: Evaluate individual terms.</strong> $b_0=1-1/2=1/2$. $b_1=1/2-1/3=(3-2)/6=1/6$. $b_2=1/3-1/4=(4-3)/12=1/12$. More generally, a common denominator gives $b_t=1/((t+1)(t+2))\gt0$.</p>
<p><strong>Step 2: Write the cancellation explicitly.</strong></p>
<div class="math-block">$$\begin{aligned}
\sum_{t=0}^{2}b_t
&=(1-\tfrac12)+(\tfrac12-\tfrac13)+(\tfrac13-\tfrac14)\\
&=1-\tfrac14=\tfrac34.
\end{aligned}$$</div>
<p>The $-1/2$ cancels $+1/2$, and $-1/3$ cancels $+1/3$. As an independent arithmetic check, $1/2+1/6+1/12=(6+2+1)/12=3/4$.</p>
<p><strong>Step 3: Identify the last index.</strong> A $T$-term sum starting at $0$ ends at $T-1$, whose second fraction is $1/(T+1)$. Every intermediate fraction appears with both signs, so $\sum_{t=0}^{T-1}b_t=1-1/(T+1)$. At $T=0$, both the empty sum and this expression are zero.</p>
<p><strong>Step 4: Take the limit of partial sums.</strong> As $T\to\infty$, $1/(T+1)\to0$, giving the infinite sum $1$. The omitted tail is exactly $1/(T+1)$. All terms are positive, so the partial sums increase, but the formula keeps them below $1$. Positivity implies increase, not unbounded growth. This cancellation pattern later turns many one-step energy inequalities into finite total budgets.</p>''')

add('bounds', 'GB1', 'Easy', 'Compute bounds and extrema on a finite set',
r'''<p>Let $A=\{-3,1,1,2\}$. Write it without repetitions, find its cardinality, infimum, supremum, minimum and maximum, and decide whether $-4$ is a lower bound and $5$ is an upper bound. Why are these latter bounds not the tightest ones?</p>''',
r'''<p>A set does not retain repeated entries. A lower bound must be below every member; the infimum is the greatest of all such lower bounds.</p>''',
r'''<p><strong>Step 1: Remove the repeated listing.</strong> $A=\{-3,1,2\}$, so $|A|=3$. Listing $1$ twice does not create a fourth distinct element.</p>
<p><strong>Step 2: Find the tight lower bound.</strong> Every member is at least $-3$, so $-3$ is a lower bound. A proposed larger lower bound would exceed the actual member $-3$, and would fail its test. Thus $\inf A=-3$. It is a member of $A$, so $\min A=-3$ too.</p>
<p><strong>Step 3: Find the tight upper bound.</strong> Every member is at most $2$, so $2$ is an upper bound. A proposed smaller upper bound would fail at the member $2$. Thus $\sup A=2$, and because it belongs to the set, $\max A=2$.</p>
<p><strong>Step 4: Check looser bounds.</strong> $-4$ is indeed a lower bound: $-4\le-3$, $-4\le1$, $-4\le2$. But the larger lower bound $-3$ works, so $-4$ is not the greatest lower bound. Likewise $5$ is an upper bound, but $2$ is a smaller upper bound, so $5$ is not the least upper bound.</p>
<p><strong>Step 5: State the distinction.</strong> Lower and upper bounds need not be members. Minimum and maximum must be members. Every nonempty finite subset of $\mathbb R$ has a smallest and a largest member; infinite sets require a separate attainment check.</p>''')

add('bounds', 'GB2', 'Medium', 'Prove a supremum with an arbitrary gap',
r'''<p>For $A=\{2-1/n:n=1,2,\dots\}$, prove that $\sup A=2$ using an arbitrary gap $\varepsilon\gt0$. Find the minimum, explain why there is no maximum, and exhibit a member larger than $1.99$.</p>''',
r'''<p>Show first that $2$ bounds every element, then that each smaller candidate ceiling is exceeded. For the latter, choose $n\gt1/\varepsilon$.</p>''',
r'''<p><strong>Step 1: Establish an upper bound.</strong> Every index $n\ge1$ is finite and positive, so $1/n\gt0$. Therefore $2-1/n\lt2$ for every member, and $2$ is an upper bound.</p>
<p><strong>Step 2: Rule out every smaller upper bound.</strong> Take any $\varepsilon\gt0$, so the proposed smaller bound is $2-\varepsilon$. Choose an integer $n\gt1/\varepsilon$, possible because integers are unbounded. Taking positive reciprocals gives $1/n\lt\varepsilon$, hence $2-1/n\gt2-\varepsilon$. We have found a member exceeding that proposed bound. Every number below $2$ has this form for some positive gap, so no smaller upper bound exists. Thus $\sup A=2$.</p>
<p><strong>Step 3: Check attainment separately.</strong> No member equals $2$, since that would require $1/n=0$. There is also a direct larger member after each one: $1/(n+1)\lt1/n$, so $2-1/(n+1)\gt2-1/n$. Consequently no maximum exists.</p>
<p><strong>Step 4: Find the bottom of the set.</strong> Since $1/n\le1$, every member is at least $1$. At $n=1$, it equals $1$. Therefore $\min A=\inf A=1$.</p>
<p><strong>Step 5: Make the gap argument concrete.</strong> To exceed $1.99=2-0.01$, require $n\gt100$. Choosing $n=101$ gives $2-1/101\gt1.99$. At $n=100$ the value is exactly $1.99$, so that index would fail the strict request. The general proof and this numerical instance use the same reasoning.</p>''')

add('bounds', 'GB3', 'Easy', 'Separate a minimum value from a minimizer',
r'''<p>On $D=\{-1,0,1,2\}$, let $f(x)=(x-1)^2$. Find $f(D)$, $\min_{x\in D}f(x)$ and $\operatorname*{arg\,min}_{x\in D}f(x)$. Repeat the last two calculations on $D'=\{0,2\}$. Explain the type of each answer.</p>''',
r'''<p>Make a table of input-output pairs. The minimum is an output value; argmin is the set of inputs attaining it.</p>''',
r'''<p><strong>Step 1: Evaluate every permitted input.</strong> $f(-1)=(-2)^2=4$, $f(0)=(-1)^2=1$, $f(1)=0^2=0$, and $f(2)=1^2=1$. Thus the output set is $f(D)=\{0,1,4\}$; its repeated value $1$ is listed once.</p>
<p><strong>Step 2: Find the smallest output.</strong> The smallest of those output values is $0$. Hence $\min_{x\in D}f(x)=0$. This answer is a real number measured on the output side.</p>
<p><strong>Step 3: Collect all attaining inputs.</strong> Only $x=1$ has output $0$, so $\operatorname*{arg\,min}_{x\in D}f(x)=\{1\}$. The answer is a set of inputs, even when it has just one member. The input $1$ and the minimum value $0$ play different roles.</p>
<p><strong>Step 4: Change the permitted inputs.</strong> On $D'=\{0,2\}$, both outputs equal $1$. The minimum value is now $1$, and the argmin set is $\{0,2\}$. A well-defined minimum value need not have a unique minimizer.</p>
<p><strong>Step 5: State the general test.</strong> An input $x$ belongs to argmin exactly when it is permitted and $f(x)$ equals the minimum value. Changing a domain can change that value and the attaining set, even while the function formula stays the same.</p>''')

add('topology', 'GT1', 'Easy', 'Check open and closed as separate properties',
r'''<p>Working in the ambient space $\mathbb R$, classify $[0,1)$, $\mathbb R$, and $\emptyset$ as open or closed. Explain why “not open” does not mean “closed”. For $[0,1)$, exhibit a member without an interior neighbourhood and a convergent sequence whose limit is missing.</p>''',
r'''<p>Open means each member has a small interval around it contained in the set. Closed means all limits of convergent sequences of members are retained, or equivalently the complement is open.</p>''',
r'''<p><strong>Step 1: Test openness of $[0,1)$.</strong> The number $0$ is a member. For any radius $r\gt0$, the neighbourhood $(-r,r)$ contains $-r/2$, which is outside $[0,1)$. Thus $0$ has no neighbourhood contained in the set, and the set is not open.</p>
<p><strong>Step 2: Test closedness independently.</strong> For integers $n\ge1$, the numbers $x_n=1-1/n$ all lie in $[0,1)$. They converge to $1$, since $|x_n-1|=1/n\to0$. But $1$ is excluded, so the set is not closed either. It is therefore neither open nor closed; the two properties are not logical opposites.</p>
<p><strong>Step 3: Check the entire ambient space.</strong> For any $x\in\mathbb R$, the interval $(x-1,x+1)$ stays in $\mathbb R$, so $\mathbb R$ is open. It is also closed: every real limit belongs to $\mathbb R$, or its complement $\emptyset$ is open.</p>
<p><strong>Step 4: Check the empty set.</strong> Openness asks for a neighbourhood around each member. There are no members for which that requirement can fail, so $\emptyset$ is open. Its complement is $\mathbb R$, already proved open, so $\emptyset$ is closed too. A set may be both open and closed. These statements refer to the ambient space specified in the question; a different ambient space can change the classification.</p>''')

add('topology', 'GT2', 'Medium', 'Choose delta in a continuity proof',
r'''<p>For $f(x)=2x+1$, prove continuity at an arbitrary real point $a$ using the epsilon-delta definition. State how $\delta$ depends on a given $\varepsilon\gt0$. At $a=1$ and $\varepsilon=0.1$, give a concrete input interval and its output interval.</p>''',
r'''<p>Subtract $f(a)$ before estimating. Continuity at $a$ asks for $|f(x)-f(a)|\lt\varepsilon$ whenever $|x-a|\lt\delta$.</p>''',
r'''<p><strong>Step 1: State the goal and its choice order.</strong> Fix any point $a\in\mathbb R$. For each tolerance $\varepsilon\gt0$, we must find $\delta\gt0$ so that every input within distance $\delta$ of $a$ has its output within distance $\varepsilon$ of $f(a)$. The output tolerance is given first; the input tolerance is chosen in response.</p>
<p><strong>Step 2: Simplify the exact output difference.</strong> Subtracting the two formulas cancels the constant:</p>
<div class="math-block">$$|f(x)-f(a)|=|(2x+1)-(2a+1)|=|2(x-a)|=2|x-a|.$$</div>
<p><strong>Step 3: Choose and verify a radius.</strong> Set $\delta=\varepsilon/2$, which is positive. If $|x-a|\lt\delta$, multiplying by $2$ gives $|f(x)-f(a)|=2|x-a|\lt2\delta=\varepsilon$. This proves continuity at $a$. Because $a$ was arbitrary, the function is continuous on all of $\mathbb R$.</p>
<p><strong>Step 4: Substitute the numerical tolerance.</strong> At $a=1$, $f(a)=3$. For $\varepsilon=0.1$, our radius is $\delta=0.05$. Inputs satisfying $|x-1|\lt0.05$ lie in $(0.95,1.05)$; applying $2x+1$ gives outputs in $(2.9,3.1)$, exactly the required distance less than $0.1$ from $3$.</p>
<p><strong>Step 5: Track the endpoints.</strong> Inputs equal to $0.95$ or $1.05$ give output distance exactly $0.1$, so they are excluded by this strict version of the definition. A smaller positive $\delta$ would also work; existence of a suitable radius is the requirement, not uniqueness.</p>''')

add('topology', 'GT3', 'Medium', 'Derive a Lipschitz constant on a stated domain',
r'''<p>Prove that $f(x)=x^2$ is $4$-Lipschitz on $[0,2]$ using the factorization of $x^2-y^2$. Show why no finite Lipschitz constant works on all of $\mathbb R$. Does this prevent the function from being continuous?</p>''',
r'''<p>On a bounded domain you can bound $|x+y|$. On the whole real line, test the pair $x=n+1,y=n$ and let $n$ grow.</p>''',
r'''<p><strong>Step 1: State what must hold for every pair.</strong> A Lipschitz constant $L$ on a domain requires $|f(x)-f(y)|\le L|x-y|$ for every pair of points in that domain. A few successful pairs do not prove the universal requirement.</p>
<p><strong>Step 2: Factor the output difference.</strong> For real $x,y$, $x^2-y^2=(x-y)(x+y)$, so $|x^2-y^2|=|x-y||x+y|$. For $x,y\in[0,2]$, their sum lies in $[0,4]$, giving $|x+y|\le4$. Therefore $|x^2-y^2|\le4|x-y|$, as required. The same inequality holds when $x=y$, with both sides zero.</p>
<p><strong>Step 3: Test a proposed global constant.</strong> Suppose a finite $L\ge0$ worked on $\mathbb R$. For any nonnegative integer $n$, choose $x=n+1$ and $y=n$. Their input distance is $1$, but their output distance is $(n+1)^2-n^2=2n+1$. The Lipschitz requirement would give $2n+1\le L$ for every such $n$. Choosing an integer larger than $L$ contradicts this. Thus no finite global constant exists.</p>
<p><strong>Step 4: Keep continuity distinct.</strong> The function is nevertheless continuous at each real $a$. For example, choose $\delta=\min\{1,\varepsilon/(2|a|+1)\}$ for any $\varepsilon\gt0$. If $|x-a|\lt\delta$, then $|x+a|\le|x-a|+2|a|\lt1+2|a|$, so $|x^2-a^2|=|x-a||x+a|\lt\delta(1+2|a|)\le\varepsilon$. The permitted radius can depend on $a$; a global Lipschitz constant would have to control every pair with one finite number.</p>''')

add('rates', 'GR1', 'Easy', 'Read the quantifiers behind big-O',
r'''<p>Let $f(n)=3n+4$ for integers $n\ge1$. Prove $f(n)=O(n)$ with an explicit constant $C$ and threshold $n_0$. Would $C=3$ work at any finite threshold? Would $C=4$ work, and from which threshold?</p>''',
r'''<p>$O(n)$ requires $f(n)\le Cn$ for every integer $n\ge n_0$, for some fixed $C\gt0$ and $n_0$. Divide by positive $n$ to inspect $3+4/n$.</p>''',
r'''<p><strong>Step 1: State the required witness.</strong> We need one constant $C\gt0$ and one integer $n_0\ge1$ such that $3n+4\le Cn$ for every $n\ge n_0$. The constant cannot change with $n$ after it is chosen.</p>
<p><strong>Step 2: Give an easy pair of witnesses.</strong> For $n\ge1$, $4\le4n$. Hence $3n+4\le3n+4n=7n$. Choosing $C=7$ and $n_0=1$ proves $f(n)=O(n)$.</p>
<p><strong>Step 3: Check the tempting smaller constant.</strong> If $C=3$, the inequality would require $3n+4\le3n$, or $4\le0$, at every permitted $n$. It fails even at arbitrarily large finite indices. The limiting ratio $f(n)/n\to3$ does not make $3$ a valid upper-bound constant.</p>
<p><strong>Step 4: Trade a smaller constant for a later threshold.</strong> For $C=4$, the condition becomes $3n+4\le4n$, equivalently $n\ge4$. Thus $C=4$ works with $n_0=4$. At $n=3$, $f(3)=13\gt12=4(3)$, so any smaller threshold would include a failing index.</p>
<p><strong>Step 5: Interpret the notation.</strong> Big-O records the existence of some working constant and threshold; it does not specify their smallest values or assert an exact equality $f(n)=Cn$. Different valid witnesses can describe the same growth class.</p>''')

add('rates', 'GR2', 'Easy', 'Divide cumulative growth by the number of trials',
r'''<p>For $T\ge1$, compare cumulative quantities $A_T=100\sqrt T$, $B_T=100T$, and $C_T=100$. Find their averages after $T$ trials, their values at $T=10^4$, and decide which cumulative quantities are $o(T)$. Can a cumulative quantity increase without bound while its average tends to zero?</p>''',
r'''<p>An average divides the total by $T$. Little-o of $T$ means that this ratio tends to zero, not that the total tends to zero.</p>''',
r'''<p><strong>Step 1: Form the three ratios.</strong> Division by $T\gt0$ gives $A_T/T=100/\sqrt T$, $B_T/T=100$, and $C_T/T=100/T$. In the first ratio, $\sqrt T/T=1/\sqrt T$ because $T=(\sqrt T)^2$.</p>
<p><strong>Step 2: Substitute a finite budget.</strong> At $T=10^4=10{,}000$, $\sqrt T=100$. The totals are $A_T=10{,}000$, $B_T=1{,}000{,}000$, and $C_T=100$. The respective averages are $1$, $100$, and $0.01$.</p>
<p><strong>Step 3: Test the limiting ratios.</strong> As $T\to\infty$, $100/\sqrt T\to0$ and $100/T\to0$, so $A_T=o(T)$ and $C_T=o(T)$. The middle ratio remains $100$, so $B_T$ is not $o(T)$; it is proportional to $T$.</p>
<p><strong>Step 4: Explain what sublinear means.</strong> $A_T=100\sqrt T$ grows without bound, yet it grows more slowly than the number of trials. Its average tends to zero. The vanishing average therefore does not mean that accumulated error or regret disappears, nor that every individual trial has a vanishing value. It compares a total with a growing horizon.</p>''')

add('rates', 'GR3', 'Medium', 'Find the accuracy where a better rate becomes cheaper',
r'''<p>Two sufficient error bounds are $E_A(T)\le1000/T$ and $E_B(T)\le1/\sqrt T$ for integer budgets $T\ge1$. Compare the bounds at $T=10^4$ and $T=10^8$. Find where the two formulas cross, then compute the smallest sufficient budgets for tolerances $0.01$ and $0.0001$. Assume equal work per iteration.</p>''',
r'''<p>Solve each error-bound inequality separately. The constants matter at finite budgets even though $1/T$ decays faster than $1/\sqrt T$.</p>''',
r'''<p><strong>Step 1: Compare actual bound values.</strong> At $T=10^4$, algorithm A's bound is $1000/10{,}000=0.1$, while B's is $1/100=0.01$, so B has the smaller bound. At $T=10^8$, A's is $10^{-5}$, while B's is $10^{-4}$, so A has the smaller bound.</p>
<p><strong>Step 2: Solve the crossover exactly.</strong> Equality $1000/T=1/\sqrt T$ is equivalent to $1000=\sqrt T$, after multiplying by $T\gt0$. Squaring gives $T=10^6$. Before this budget B's formula is smaller; afterwards A's is smaller. This compares the guarantees, not necessarily the observed errors.</p>
<p><strong>Step 3: Solve for a requested positive tolerance.</strong> To certify error at most $\varepsilon$, A needs $1000/T\le\varepsilon$, hence $T\ge1000/\varepsilon$. B needs $1/\sqrt T\le\varepsilon$, hence $T\ge1/\varepsilon^2$. For a general tolerance, round each lower bound up to the next integer and enforce $T\ge1$.</p>
<p><strong>Step 4: Substitute both tolerances.</strong> At $\varepsilon=0.01$, A needs $100{,}000$ iterations and B needs $10{,}000$, so B uses one tenth of the work under equal per-iteration cost. At $\varepsilon=0.0001$, A needs $10{,}000{,}000$ and B needs $100{,}000{,}000$, so A now uses one tenth.</p>
<p><strong>Step 5: Explain the change.</strong> The ratio of the formulas is $(1000/T)/(1/\sqrt T)=1000/\sqrt T\to0$, so A has the faster asymptotic decay. Its larger constant delays the benefit. A rate comparison must retain constants and the requested accuracy to justify a finite work budget.</p>''')


assert len(EXERCISES) == 30
assert len({e['code'] for e in EXERCISES}) == 30
