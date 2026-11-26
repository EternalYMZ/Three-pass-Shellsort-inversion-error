# The parity-pass deficit

For a uniform permutation and the gap word $(h,2,1)$, write $D=n\psi(h,2)-\mathbb E M_3$. For odd $h\ge3$ this is positive except for equality at $(n,h)=(2,3)$. The analytic bound is uniform in $n\ge h$ as $h$ tends to infinity. Put $\rho=n/h$, $m=\lfloor\rho\rfloor$, and $\theta=\rho-m$. Then

$$
\frac{D}{h^{3/2}}=
\frac{\rho}{2\sqrt{2\pi}}\int_0^1
\left(1-\sqrt{1-(1-\theta)y^{2m}-\theta y^{2m+2}}\right)dy
+O((1+\log h)/\sqrt h).
$$

The curve attains its unique minimum $(1-\pi/4)/(2\sqrt{2\pi})$ at $\rho=1$ and approaches its supremum $(1-\log2)/(2\sqrt{2\pi})$ as $\rho$ tends to infinity. Every integer ratio of at least two is a strict local minimum. These statements have analytical proofs.

Run the finite check with Python 3.9 or newer from the repository root.

~~~sh
python research/parity-profile/check_parity_profile.py
~~~

It integrates the threshold polynomial in exact arithmetic and compares it with ordinary insertion. All 137,790 permutation/table pairs with odd $3\le h\le n\le8$ agree. Two quadrature orders independently evaluate the limiting integral; rational values are supplied for the finite deficit. [Reproduced values](results.txt) · [Janson and Knuth, §10](https://arxiv.org/pdf/cs/9608105#page=15)
