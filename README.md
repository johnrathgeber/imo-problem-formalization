# A proof of IMO 1998 Q3, formalized in Lean.

For any positive integer $n$, let $d(n)$ denote the number of positive divisors
of $n$. Determine all positive integers $k$ such that $\frac{d(n^2)}{d(n)} = k$ for some $n$.

The answer to this problem is $k$ can be any odd number. To formalize this,
we must prove that if a $k$ satisfies $\frac{d(n^2)}{d(n)} = k$ for some $n$, then
$k$ is odd, and also that if $k$ is odd, it satisfies $\frac{d(n^2)}{d(n)} = k$ for some $n$.

We follow Evan Chen's proof: <https://web.evanchen.cc/exams/IMO-1998-notes.pdf>.

Throughout this proof, we will use the following facts from number theory:
* $d(ab) = d(a)d(b)$ when $a$ and $b$ are coprime
* $p_1^{k_1}$ is coprime to $p_2^{k_2}$ when both $p_1$ and $p_2$ are prime, $p_1 \neq p_2$, and $k_1, k_2 \geq 0$.
* $d(p^k) = k + 1$ for prime $p$ and $k \geq 1$

### Necessity: $\left(\exists n > 0, \frac{d(n^2)}{d(n)} = k\right) → k \equiv 1 \pmod{2}$. 

To prove this, we write $n$ in its prime factorization as 
$$n = \prod_{i=1}^tp_i^{k_i}$$
Then, using the above number theory facts, we can write
$$d(n) = d\left(\prod_{i=1}^tp_i^{k_i}\right) = \prod_{i=1}^td\left(p_i^{k_i}\right) = \prod_{i=1}^t(k_i + 1)$$
$$d(n^2) = d\left(\prod_{i=1}^tp_i^{2k_i}\right) = \prod_{i=1}^td\left(p_i^{2k_i}\right) = \prod_{i=1}^t(2k_i + 1)$$
so
$$k = \frac{d(n^2)}{d(n)} = \prod_{i=1}^t\frac{2k_i + 1}{k_i + 1}$$
Since the numerator is always odd, $k$ is always odd. This concludes the proof of necessity.

### Sufficiency: $k \equiv 1 \pmod{2} \rightarrow \left(\exists n > 0, \frac{d(n^2)}{d(n)} = k\right)$.

We prove this by strong induction.

Base Case: $k = 1$. $n = 1$ works.

Inductive Step: Assume $k > 1$, and $\forall j < k, j \equiv 1 \pmod{2} \to \exists n > 0, \frac{d(n^2)}{d(n)} = j$. Let $k = 2^tj - 1$ be odd, where $j$ is also odd. We can write $k$ in this way because every even number has both an even and an odd part, and since $k + 1$ is even, we can let $2^t$ be its even part and $j$ be its odd part. In particular, $t$ will be the power $2$ is raised to in $k+1$'s prime factorization.

We get $j < k$ immediately, so by our inductive hypothesis,
$$\exists n_j > 0, \frac{d(n_j^2)}{d(n_j)} = j$$

We now aim to construct a number $x$ such that $\frac{d((n_jx)^2)}{d(n_jx)} = k$. Let
$$x = \prod_{i=0}^{t-1} p_i^{2^{t + i}j - 2^i(j + 1)}$$
where each $p_i$ is prime, distinct, and does not appear as a prime in $n_j$'s prime factorization. This is justified by the infinitude of primes. We also have that $d\left(p_i^{2^{t + i}j - 2^i(j + 1)}\right) = (2^{t + i}j - 2^i(j + 1)) + 1 \, \forall i$, as $2^{t + i}j - 2^i(j + 1) \geq 1\, \forall i$. Then we can compute
$$\frac{d(x^2)}{d(x)} = \prod_{i=0}^{t-1}\frac{2(2^{t + i}j - 2^i(j + 1)) + 1}{(2^{t + i}j - 2^i(j + 1)) + 1} = \prod_{i=0}^{t-1}\frac{2^{t + i + 1}j - 2^{i + 1}(j + 1) + 1}{2^{t+i}j - 2^i(j + 1) + 1}$$
$$ = \frac{2^{2t}j-2^t(j+1)+1}{2^{2t-1}j-2^{t-1}(j+1)+1}\cdot \frac{2^{2t-1}j-2^{t-1}(j+1)+1}{2^{2t-2}j-2^{t-2}(j+1)+1}\cdot\cdots\cdot\frac{2^{t+1}j-2(j+1)+1}{2^tj-(j+1)+1}$$
Which telescopes cleanly to
$$= \frac{2^{2t}j-2^t(j+1)+1}{2^tj-(j+1)+1} = \frac{(2^tj-1)(2^t-1)}{j(2^t-1)} = \frac{2^tj-1}{j}$$

We can multiply both sides by $j$ to achieve
$$k = 2^tj - 1 = j \cdot \frac{d(x^2)}{d(x)} = \frac{d(n_j^2)d(x^2)}{d(n_j)d(x)} = \frac{d((n_jx)^2)}{d(n_jx)}$$
where the last equality holds because each prime in $x$'s factorization does not appear in $n_j$'s factorization, so $x$ and $n_j$ are coprime, and similarly for $x^2$ and $n_j^2$. This concludes the proof of sufficiency.

Since we have proven both necessity and sufficiency, we know
$$k \equiv 1 \pmod{2} \iff \left(\exists n > 0, \frac{d(n^2)}{d(n)} = k\right)$$
as desired.