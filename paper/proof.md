# Disjoint-union-free uniform hypergraphs: the coefficient-one threshold for fixed rank at least three

**Yilin Liu**

*27 September 2026.*

**Abstract.** Let $g_r(n)$ be the largest size of an $r$-uniform family with no two distinct partitions of the same $2r$-set into disjoint edges. We prove $g_3(n)\le\binom n2$ for every $n$ and, for each fixed $r\ge4$, prove $g_r(n)=\binom{n-1}{r-1}+\lfloor(n-1)/r\rfloor$ for all sufficiently large $n$. Hence the least forcing threshold is asymptotic to $\binom n{r-1}$ for every fixed $r\ge3$.

## I. Problem and the all-rank theorem

An admissible $r$-graph $H\subseteq\binom Vr$ contains no four distinct edges $A,B,C,D$ with

$$
A\cap B=C\cap D=\varnothing,\qquad A\cup B=C\cup D.
$$

For disjoint sets, concatenation denotes union; a vertex in such an expression denotes its singleton. Write $A-x=A\setminus\\{x\\}$. For any $j$, let $d_H(S)=|\\{E\in H:S\subseteq E\\}|$ and $\Delta_j(H)=\max_{|S|=j}d_H(S)$, taking an empty maximum as zero. The $j$-shadow $\partial_jH$ is the family of $j$-sets contained in an edge of $H$; write $\partial H=\partial_{r-1}H$.
Let $g_r(n)$ be the maximum number of edges of such a family on $n$ vertices, and set $F_r(n)=g_r(n)+1$. Erdős problem #643 [1], recorded as JSP-000523 [2], asks whether $F_r(n)=(1+o(1))\binom n{r-1}$ for every fixed $r\ge3$.

**Theorem 1 (main theorem).** Every admissible triple system on $n$ vertices has at most $\binom n2$ edges. For every fixed $r\ge4$ and every sufficiently large $n$,

$$
g_r(n)=\binom{n-1}{r-1}+\left\lfloor\frac{n-1}{r}\right\rfloor.
$$

Thus, for every fixed $r\ge3$,

$$
F_r(n)=(1+o(1))\binom n{r-1}.
$$

For $r\ge4$ the eventual equality families are the two forms proved in Parts III and IV.

**Common construction.** Fix a vertex $v$, take every $r$-set through $v$, and add a matching of $\lfloor(n-1)/r\rfloor$ $r$-sets avoiding $v$. If a union of two disjoint edges omits $v$, the matching blocks determine its partition. If it contains $v$, each partition has exactly one outside matching block; two different blocks would occupy $2r$ of the only $2r-1$ points outside $v$ in that union. Thus the construction is admissible and has the displayed number of edges. In particular, the full triple star has $\binom{n-1}{2}$ edges.

Part I gives a coarse bound; Parts II–IV treat ranks three, four, and at least five, respectively.

### I.1 A self-contained coarse bound

We use the finite Cauchy inequality
$(\sum_i a_ib_i)^2\le(\sum_i a_i^2)(\sum_i b_i^2)$.
It follows by expanding $\sum_i(a_i-tb_i)^2\ge0$ and requiring its quadratic discriminant to be nonpositive; the case $\sum_i b_i^2=0$ is immediate.

**Theorem I.1 (finite coarse bound).** For every admissible $r$-uniform family $H$ on $n$ vertices, where $r\ge3$ and $n\ge0$,

$$
\boxed{r!\\,|H|\le 3r^r n^{r-1}.}
\tag{I.1}
$$

Thus $|H|\le K_r n^{r-1}$ with $K_r=3r^r/r!$. In particular,

$$
|H|\le32n^3\qquad(r=4).
\tag{I.2}
$$

The rank-four instance will also apply to induced subfamilies.

#### Graph deletion

For a finite simple graph $G$, let $D(G)$ be the unordered vertex pairs with at least two common neighbors, called diagonals.

**Lemma I.2.** One can delete at most $|D(G)|$ edges to obtain a graph with no four-cycle.

**Proof.** Induct on $|E(G)|$. If $D(G)=\varnothing$, stop. Otherwise choose an edge $uv$ on a four-cycle and set

$$
X=N(v)\cap\\{x:ux\in D(G)\\},\qquad
Y=N(u)\cap\\{y:vy\in D(G)\\}.
$$

Both sets are nonempty and avoid $u,v$. Delete the $|X|+|Y|$ distinct edges $vx$ and $uy$.

Every former diagonal $ux$ with $x\in X$ now has no common neighbor: a surviving common neighbor $w$ would differ from $v$; originally $u,x$ were two common neighbors of $v,w$, so $w\in Y$ and $uw$ was deleted. The argument for $vy$, $y\in Y$, is symmetric. These are $|X|+|Y|$ distinct diagonals, and deletion creates none. Apply induction to the remaining graph; its deletion budget plus the first batch is at most $|D(G)|$. ∎

This deletion lemma also appears in [3, Lemma 3].

#### Three-partite triple systems

Let $T\subseteq A\times B\times C$ be viewed as a triple system on three disjoint vertex classes. Write

$$
a=|A|,\quad b=|B|,\quad c=|C|,\quad N=a+b+c,
$$

$$
S=\binom a2+\binom b2+\binom c2,\qquad
P=ab+ac+bc.
$$

**Lemma I.3.** If $T$ is admissible, then

$$
\boxed{3|T|\le P+4S.}
\tag{I.3}
$$

In particular, if $a,b,c\le n$, then $|T|\le3n^2$.

**Proof.**

**Diagonals have only one possible link.**

For two distinct vertices $x,y$, let

$$
J_{xy}(T)=\\{Q:|Q|=2,\ xQ,yQ\in T,\ Q\cap\\{x,y\\}=\varnothing\\}.
$$

This is an intersecting graph: disjoint $Q,Q'$ would give the forbidden pairs $xQ,yQ'$ and $yQ,xQ'$.

If this family is nonempty, $x,y$ are in the same vertex class and its edges run between the other two classes. Thus it is bipartite. Every intersecting bipartite graph with at least two edges is a star with a unique center. Indeed two intersecting edges $zu,zv$ have $u,v$ in the same class; an edge avoiding $z$ would have to be $uv$, which is impossible in a bipartite graph.

For a vertex $z$, let $L_z$ be its ordinary link graph. If $xy$ is a diagonal of $L_z$, the graph $J_{xy}(T)$ contains two distinct edges incident with $z$. Its unique center is therefore $z$. The same pair $xy$ cannot be a diagonal in another vertex link. Every such pair is within a vertex class. Consequently

$$
\sum_z |D(L_z)|\le S.
\tag{I.4}
$$

**Delete all link four-cycles, then count completions.**

For each original link $L_z$, apply the graph deletion lemma and choose an edge set $R_z$ of size at most $|D(L_z)|$ whose deletion removes its four-cycles. Delete from $T$ every triple $zQ$ with $Q\in R_z$, and call the remainder $T_0$. These choices all refer to the original links. Their union deletes at most $S$ triples by (I.4), and every link of $T_0$ is four-cycle-free, because it is a subgraph of the corresponding $L_z\setminus R_z$.

Now $|J_{xy}(T_0)|\le1$ for every pair. Otherwise its intersecting bipartite graph contains two edges $zu,zv$; the four triples $xzu,yzu,xzv,yzv$ give a four-cycle with opposite pair $xy$ in $L_z(T_0)$.

Let $d(Q)$ be the number of completions of a two-set $Q$ in $T_0$. The exact common-link identity gives

$$
\sum_Q\binom{d(Q)}2=\sum_{x<y}|J_{xy}(T_0)|\le S.
\tag{I.5}
$$

Every supported pair $Q$ lies across two classes, so there are at most $P$ such pairs. For each integer $d\ge1$,

$$
d\le1+\binom d2
$$

because the difference on the right is $(d-1)(d-2)/2\ge0$. Therefore

$$
3|T_0|=\sum_Qd(Q)\le P+S.
$$

Adding back at most $S$ deleted triples proves (I.3). If every class has size at most $n$, then $P\le3n^2$ and $S\le3n(n-1)/2$, so

$$
3|T|\le9n^2-6n\le9n^2.
$$

This proves the stated simpler bound. ∎

#### Finite reduction of arbitrary rank to three parts

**Proof of Theorem I.1.**

Assume $n\ge1$; if $n=0$, the theorem is immediate.

**A crossing subfamily.**

Color each vertex with one of $r$ colors. Over all $r^n$ colorings, a fixed $r$-edge has all colors distinct in a fraction $r!/r^r$ of them. Double counting pairs consisting of a coloring and one of its crossing edges shows that some coloring has a crossing subfamily $H^\times$ with

$$
r!\\,|H|\le r^r|H^\times|.
\tag{I.6}
$$

Let $V_1,\ldots,V_r$ be its color classes. Each edge of $H^\times$ has exactly one vertex in each class.

**Disjoint blocks in the first $r-2$ classes.**

Put $s=r-2$. Pad each $V_i$, $1\le i\le s$, to a set of size $n$ using fresh dummy elements, and choose a bijection from that padded set to $[n]$. Make the choices independently over the finite set of all such bijections. For each index $j$, its inverse images in the first $s$ classes form a block $B_j$ of size $s$. These blocks are pairwise disjoint.

Call a crossing edge aligned if its vertices in $V_1,\ldots,V_s$ all have the same index. Each prescribed real vertex is uniform on $[n]$ under the corresponding bijections. Hence a fixed crossing edge is aligned in a fraction

$$
\frac{n}{n^s}=n^{-(s-1)}=n^{-(r-3)}
$$

of the choices. This is a finite counting ratio: among all bijection choices, the prescribed indices have exactly $n^s$ equally sized fibers and exactly $n$ aligned index tuples.

An aligned edge has the form $B_j\cup\\{x,y\\}$ with $x\in V_{r-1}$ and $y\in V_r$; in particular its block contains no dummy element. Represent it by the triple $(j,x,y)$. Use tagged copies to make the index symbols distinct from all original vertices. This creates a three-partite triple system $T$ on the disjoint classes

$$
[n],\quad V_{r-1},\quad V_r,
$$

each of size at most $n$.

**Admissibility survives the representation.**

Distinct represented triples give distinct original edges. If two represented triples are disjoint, they use different indices, different last-class vertices, and thus disjoint original edges. If two represented edge pairs have the same union, their indices and last-class vertices agree as sets. Replacing each index by its block preserves equality of the unions. Thus a forbidden configuration in $T$ would lift to one in $H^\times\subseteq H$.

Consequently every choice of the bijections gives an admissible $T$ and, by Lemma I.3, has at most $3n^2$ aligned edges. Averaging the aligned-edge count over all choices yields

$$
\frac{|H^\times|}{n^{r-3}}\le3n^2,
\qquad |H^\times|\le3n^{r-1}.
\tag{I.7}
$$

Together with (I.6), this proves (I.1). ∎


## II. Rank three: a signed support inequality

The support sets in this proof consist only of pairs that actually occur. The local signed graph theorem, potential-preserving dense-block removal, and nonoverlapping bridge payment are included in §§II.A–II.D.


### II.1 Setting and target

Let $H$ be a finite simple triple system on $V$. Assume that for distinct $x,y$ the common link

$$
 J_{xy}=\\{p\in\binom{V\setminus\\{x,y\\}}2:px,py\in H\\}
$$

is intersecting. Equivalently, there are no two distinct pairs of disjoint triples with the same union. Indeed, disjoint pairs $p,q$ in $J_{xy}$ give the two partitions $\\{px,qy\\}$ and $\\{py,qx\\}$. Conversely, in two different partitions of a six-set into triples, relabel the parts so that one intersection has size two; the two opposite intersections are pairs $p,q$, and the remaining points $x,y$ give this configuration.

We use the elementary classification that an intersecting simple graph is a star or a triangle (with empty and one-edge graphs allowed as stars). To see this, choose two edges $ab,ac$. Any edge avoiding $a$ must be $bc$, and then every edge lies in the triangle $abc$; if none avoids $a$ the graph is a star. In particular, an intersecting graph with at least four edges has a unique star center.

Write $xy$ for the unordered pair $\\{x,y\\}$, and $px$ for $p\cup\\{x\\}$. Define $N(p)=\\{x\in V\setminus p:px\in H\\}$. For a pair $p$, put $d(p)=|N(p)|$, and put $c(xy)=|J_{xy}|$. Let

$$
 m=|H|,\quad P=\\{p:d(p)>0\\},\quad C=\\{q:c(q)>0\\},
 \quad s=|P|,\quad t=|C|,\quad\Psi=2m-s-t.
$$

We aim to prove the stronger support inequality $\Psi\le0$; it implies $m\le\binom{|V|}{2}$.

Write $k_i$ for the number of pairs with $d=i$ and $b_i$ for the number with $c=i$. (The symbol $b_i$ is a count; the function $b(d)$ below is different.) Put

$$
 L=\sum_q(c(q)-3)_{+},\quad
 b(d)=\begin{cases}(d-2)(d-3),&d\ge4,\\\\0,&d\le3,\end{cases}
 \quad \mathcal B=\sum_p b(d(p)).
$$

### II.2 Exact support ledger

Double counting two triples through a pair gives

$$
 \sum_q c(q)=\sum_p\binom{d(p)}2.
$$

For every positive integer $d$,

$$
 \binom d2-\frac12b(d)=2d-3+\mathbf1_{\\{d=1\\}}.
$$

Summing only over used pairs yields

$$
 \sum_qc(q)-\frac12\mathcal B=6m-3s+k_1.
$$

Also, directly from the definition of $L$,

$$
 L=\sum_qc(q)-3t+2b_1+b_2.
$$

Subtracting the equations proves the exact identity

$$
 \boxed{6\Psi=2L-\mathcal B-2k_1-4b_1-2b_2.}\tag{II.1}
$$

### II.3 Signed weights at every root

For $d\ge0$ define $f(d)=(d-3)_{+}/d$ when $d>0$ and $f(0)=0$. Put $h(d)=b(d)/d$ for $d>0$ and $h(0)=0$, and let $g=f$.

For root $z$, let $G_z$ be the ordinary graph on $V\setminus\\{z\\}$ with edges $p$ for which $zp\in H$. Write $d_x=d(zx)$, and $\mu_z(x,u)=|N_{G_z}(x)\cap N_{G_z}(u)|$. For $xy\in G_z$ set

$$
 w_z(xy)=
 \sum_{u\in N_{G_z}(y)\setminus\\{x\\}}g(\mu_z(x,u))
 +\sum_{v\in N_{G_z}(x)\setminus\\{y\\}}g(\mu_z(y,v))
 -h(d_x)-h(d_y).\tag{II.2}
$$

The equivalent deficit expression is

$$
 w_z(xy)=f(d_x)+f(d_y)
 -(d_x-d_y)(f(d_x)-f(d_y))-P_{xy},\tag{II.3}
$$

where

$$
 P_{xy}=
 \sum_{u\in N(y)\setminus\\{x\\}}[f(d_x)-g(\mu_z(x,u))]
 +\sum_{v\in N(x)\setminus\\{y\\}}[f(d_y)-g(\mu_z(y,v))]\ge0.
$$

All common-neighbor counts in the first sum are at most $d_x$, and analogously in the second, proving nonnegativity.

The base term before $P$ is at most $2\min\\{f(d_x),f(d_y)\\}$: when the integer degrees differ their difference has magnitude at least one, and when equal the claim is equality. Thus:

* $w_z(xy)\le2$; if $w_z(xy)>0$ then both endpoint degrees are at least four.
* A weak alternative is an edge adjacent to $xy$ whose opposite endpoints have common-neighbor count at most three. Each weak alternative contributes at least $\min\\{f(d_x),f(d_y)\\}$ to $P$. A positive edge therefore has at most one weak alternative.
* With one weak alternative the weight is at most $\min\\{f(d_x),f(d_y)\\}<1$.

Summing (II.2) over one link gives

$$
\sum_{xy\in G_z}w_z(xy)
=2\sum_{\\{x,u\\}\subseteq V\setminus\\{z\\}}(\mu_z(x,u)-3)_{+}
-\sum_{x\ne z}b(d(zx)).
$$

For each unordered pair $\\{x,u\\}$, its common neighbors contribute twice, so its contribution is $2\mu_z(x,u)g(\mu_z(x,u))=2\max(\mu_z(x,u)-3,0)$. Each vertex $x$ contributes $d(zx)h(d(zx))=b(d(zx))$ to the negative part. A common link $J_{xu}$ with at least four edges has a unique star center $z$, and only that root has $\mu_z(x,u)>3$; at that root $\mu_z(x,u)=c(xu)$. All other common links give zero surplus at every root. Each pair budget $b(d(p))$ appears at its two endpoints. Hence summing over **all** roots gives

$$
 \sum_{z,xy\in G_z}w_z(xy)=2L-2\mathcal B.\tag{II.4}
$$

Let $W^{+},W^{-}$ denote the totals of positive weights and absolute negative weights, respectively.

For $E\in H$ define

$$
 \delta_E=\sum_{z\in E}(-w_z(E\setminus\\{z\\}))_{+}
              -\sum_{p\in\binom E2}h(d(p)).\tag{II.5}
$$

Each pair $p$ occurs in $d(p)$ triples, so

$$
 \sum_E\delta_E=W^- -\mathcal B.
$$

Consequently (II.4) becomes

$$
 \boxed{2L-\mathcal B=W^+-\sum_E\delta_E.}\tag{II.6}
$$

The local graph theorem proved in §II.A states that $\delta_E\ge0$ for every $E$. Its proof is an exact tripartite graph argument and uses no degree bound.

### II.4 Positive weights charge only $c=1$ and $c=2$ cells

A positive weight $w_z(p)$ with $d(p)=1$ is retained at $p$; it is at most two, so all such weights total at most $2k_1$.

If $d(p)\ge2$, distribute $w_z(p)/(d(p)-1)$ to each other completion pair $zv$ with $v\in N(p)\setminus\\{z\\}$. The total distributed equals the original weight. Let $\rho(q)$ be the charge received by $q$.

To see the possible receiving sizes, suppose $J_{zv}$ contains $xy$ and $xu$. In $G_z$, $xu$ is an alternative to $xy$. For every $t\in N_{G_z}(y)\cap N_{G_z}(u)$, the common link $J_{yu}$ contains $zt$, and it also contains $vx$. Intersectingness forces $t\in\\{v,x\\}$; therefore $\mu_z(y,u)\le2$. Every additional edge of $J_{zv}$ gives a weak alternative to the source $xy$. If $c(zv)\ge3$, there are at least two, so no positive weight can be sent there.

Thus only $c=1$ and $c=2$ receivers get positive charge. A $c=1$ receiver has one core $p$, two possible roots, and weight at most two from each; division by $d(p)-1$ cannot increase it. Its capacity is at most four.

A $c=2$ receiver is written uniquely as

$$
 J_{zw}=\\{xy,xu\\}.
$$

Every contributing weight is below one by the preceding weak-alternative argument. Its reciprocal satisfies

$$
 J_{yu}\supseteq\\{xz,xw\\}.\tag{II.7}
$$

### II.5 Reciprocal grouping, and the only exception

If $c(yu)=2$, applying reciprocity again returns $zw$. These receivers form disjoint unordered pairs.

Put $t_v=d(xv)$ for $v\in\\{z,w,y,u\\}$. The charge from root $v$ toward a core containing the opposite vertex $v'$ is at most

$$
 \frac{1}{t_{v'}-1}\mathbf1_{\\{t_v\ge4\\}}.
$$

Let $h_1,h_2\in\\{0,1,2\\}$ be the numbers of $t_v\ge4$ on sides $\\{z,w\\}$ and $\\{y,u\\}$. The combined charge to the two reciprocal receivers is at most

$$
 h_1(2-2h_2/3)+h_2(2-2h_1/3)
 =2(h_1+h_2)-4h_1h_2/3\le4.
$$

The last inequality is immediate for $h_i\in\\{0,1,2\\}$; its largest value is four. Thus the pair's total capacity is two per receiver.

If $c(yu)\ge3$ and $J_{yu}$ is a star, it is centered at $x$. Its at least three leaves are completions of both $xy$ and $xu$. Thus $d(xy),d(xu)\ge3$, and the four source contributions sum to at most

$$
 \frac2{d(xy)-1}+\frac2{d(xu)-1}\le2.
$$

The sole remaining case is the exact triangle

$$
 J_{yu}=\\{xz,xw,zw\\}.
$$

Define

$$
 \Xi=\sum_{\substack{J_{zw}=\\{xy,xu\\}\\\\J_{yu}=\\{xz,xw,zw\\}}}
                   (\rho(zw)-2)_{+},
$$

where every receiving pair $zw$ occurs once. The total positive capacity is therefore

$$
 \boxed{W^+\le2k_1+4b_1+2b_2+\Xi.}\tag{II.8}
$$

Combining (II.1), (II.6), and (II.8) proves the unconditional exact support reduction

$$
 \boxed{6\Psi\le\Xi-\sum_{E\in H}\delta_E.}\tag{II.9}
$$

### II.6 Remove the only bridge-overlap obstruction

§II.B, Theorem II.B.2, proves the following: simultaneously delete every triple containing a pair of any five-element block with nine or ten triples. The remaining $H_0$ satisfies

$$
 \Psi(H_0)-\Psi(H)\ge2b_9^{\rm block}+R_3\ge0,
$$

and no five-element subset of $H_0$ spans nine or ten triples. This works with arbitrary interfaces and arbitrary pair degrees.

It suffices to prove $\Psi\le0$ for $H_0$. From this point through the application of (II.9), all degrees, common links, weights, charges, $\delta$, and $\Xi$ are recomputed in $H_0$. For such a system, consider an exceptional receiver $zw$ with book base $\\{x,z,w\\}$ and pages $\\{y,u\\}$. Its four individual charges are $\alpha_y,\beta_y,\alpha_u,\beta_u$, where

$$
 \alpha_y=\frac{(w_z(xy))_{+}}{d(xy)-1},\quad
 \beta_y=\frac{(w_w(xy))_{+}}{d(xy)-1},
$$

and similarly for $u$. Each is at most one. Its bridge demands are

$$
 \gamma(zw,zwy)=\min(\alpha_y,\beta_y),\qquad
 \gamma(zw,zwu)=\min(\alpha_u,\beta_u).
$$

Since the two maxima are at most two in total,

$$
 (\rho(zw)-2)_{+}\le\gamma(zw,zwy)+\gamma(zw,zwu).\tag{II.10}
$$

By Theorem II.C.1, each triple receives positive $\gamma$ from at most one receiving pair.

Write $\gamma_E$ for the unique positive demand on $E$, or zero if there is none. Then

$$
 \Xi\le\sum_E\gamma_E.\tag{II.11}
$$

### II.7 Local bridge payment

The local bridge-payment lemma is

$$
 \boxed{\delta_E\ge\gamma(q,E)\quad\text{whenever }\gamma(q,E)>0.}\tag{II.12}
$$

Its exact graph formulation is as follows. At bridge $E=act$ for receiver $at$ with

$$
 J_{at}=\\{bc,bx\\},\qquad J_{cx}=\\{ab,bt,at\\},
$$

use auxiliary parts

$$
 X=N(at)\setminus\\{c\\},\quad
 Y=N(ac)\setminus\\{t\\},\quad
 Z=N(ct)\setminus\\{a\\}.
$$

The marked $X$-node $x$ has its two neighbors $Y_b,Z_b$. When the bridge demand is positive, their relevant degrees $r,s$ are at least three, and their neighborhoods in $X$ intersect exactly at $x$. A marked-node strengthening of the local signed graph theorem gives

$$
 \delta_E\ge\min\\{\phi(r),\phi(s)\\},\qquad
 \phi(j)=(j-2)_{+}/(j+1).
$$

The source-weight bounds $w_a(bc)\le\phi(r)$, $w_t(bc)\le\phi(s)$, together with $d(bc)-1\ge1$, then imply (II.12).

### II.8 The general finite theorem

**Theorem II.1 (rank-three support inequality).** For every integer $n\ge0$ and every admissible simple triple system $H$ on $n$ vertices,

$$
\boxed{2|H|\le |P(H)|+|C(H)|\le2\binom n2.}
$$

In particular, $|H|\le\binom n2$.

**Proof.** By (II.12), $\delta_E\ge0$ for uncharged triples and $\delta_E\ge\gamma_E$ for charged triples. Hence (II.11) gives

$$
\Xi\le\sum_E\gamma_E\le\sum_E\delta_E.
$$

Equation (II.9) implies $\Psi(H_0)\le0$. The block-removal inequality gives $\Psi(H)\le\Psi(H_0)$, proving the first inequality. The second follows from $P(H),C(H)\subseteq\binom V2$. ∎


**Corollary II.2.** For $n\ge3$,

$$
\binom{n-1}{2}\le g_3(n)\le\binom n2,
\qquad g_3(n)=(1+o(1))\binom n2.
$$

**Proof.** The upper bound is Theorem II.1. The full triple star has $\binom{n-1}{2}$ edges and is admissible because its edges intersect. ∎

### II.A. The signed local graph theorem

This appendix proves $\delta_E\ge0$ from (II.5). Its equations are numbered (II.A.1)–(II.A.9).

#### II.A.1 Exact graph reduction

At $E=\\{a,b,c\\}$, form the tagged tripartite graph $K$ with parts

$$
A=N(bc)\setminus\\{a\\},\quad B=N(ac)\setminus\\{b\\},\quad
C=N(ab)\setminus\\{c\\},
$$

joining $A_x B_y$ if $cxy\in H$, and cyclically. All labels in the parts lie outside $E$; copies of the same label in different parts are distinct vertices of $K$. Every node meeting both other parts has degree exactly two. For example, if $A_x$ meets $B_y$ and $C_z$, then $bc,cy,bz$ lie in $J_{ax}$. Intersectingness of $cy$ and $bz$ forces $y=z$, since all these labels avoid the central triple. The resulting triangle $\\{bc,by,cy\\}$ in $J_{ax}$ excludes every further edge and hence every further neighbor of $A_x$. The argument for the other parts is symmetric.

The scalar function $H(n)$ below is an auxiliary budget, distinct from the hypergraph $H$. Put

$$
\phi(t)=\frac{(t-2)_{+}}{t+1},\qquad H(n)=(n-1)\phi(n)\quad(n\ge0).
$$

Thus $H(0)=H(1)=H(2)=0$, and for $n\ge1$,

$$
H(n)=n-4+\frac6{n+1}=h(n+1).
$$

For each pair of parts define

$$
T_{AB}=\sum_{v\in A\cup B}\phi(d_{K[A,B]}(v)),
$$

and define $T_{AC},T_{BC}$ cyclically. The exact signed relation is

$$
w_c(ab)=T_{AB}-H(|A|)-H(|B|),\tag{II.A.1}
$$

with the analogous formulas at the other two roots. To check (II.A.1), an $A_x$ node has $1+d_{AB}(A_x)$ common neighbors with the appropriate central vertex in $G_c$; its contribution to the signed-weight formula (II.2) is $g(1+d_{AB})=\phi(d_{AB})$. Mixed nodes have degree one in each of their two pair-type graphs, so contribute zero to every $T$.

Hence the local inequality $\delta_E\ge0$ is equivalent to

$$
\sum_{ij\in\\{AB,AC,BC\\}}[H(n_i)+H(n_j)-T_{ij}]_{+}
\ge H(n_A)+H(n_B)+H(n_C).\tag{II.A.2}
$$

Only the property “every mixed node has degree two” is needed below; no physical-label condition is used.

#### II.A.2 The two-low-vertices lemma

**Lemma II.A.1 (two low-degree vertices).** Let $G$ be a bipartite graph on parts of sizes $a,b$. If at least two vertices of $G$, across its two parts, have degree at most one, then

$$
\sum_{v\in G}\phi(d_G(v))\le H(a)+H(b).\tag{II.A.3}
$$

**Proof.**

Because $phi$ is nondecreasing, complete all edges among the vertices other than the two designated low-degree vertices. Their degrees remain at most one.

##### Two designated vertices in the same part

Suppose they belong to the $a$-part. For $a≥4,b≥2$, the other $a-2$ vertices each contribute at most $phi(b)$. The $b$ opposite vertices initially have degree $a-2$. The two possible low-vertex edges add at most

$$
\frac6{a(a-1)}
$$

to their total contribution: the increments of $phi$ are decreasing starting at degree two. Thus the total is at most

$$
S=(a-2)\phi(b)+b\phi(a-2)+\frac6{a(a-1)}.
$$

Direct simplification gives

$$
H(a)+H(b)-S
=\frac{3(a-b-2)(a-b-1)}{(a-1)(b+1)}
+\frac6{a+1}-\frac6{a(a-1)}\ge0.
$$

The consecutive-integer product is nonnegative, and the final difference is nonnegative for $a≥4$.

If $a=2$, every degree is at most two, so the sum is zero. If $a=3,b≥2$, the sum is at most $phi(b)+1/4$, while $H(b)≥phi(b)$ and $H(3)=1/2$. If $b=1$, the sum is at most $phi(a)≤H(a)$; $b=0$ is trivial.

##### One designated vertex in each part

For $a,b≥3$, complete all edges between the other $a-1$ and $b-1$ vertices. Attaching each low vertex to a high vertex is at least as good for the sum as joining the two low vertices together. Therefore the sum is at most

$$
S=(a-1)\phi(b-1)+(b-1)\phi(a-1)
+\frac3{a(a+1)}+\frac3{b(b+1)}.
$$

Exactly

$$
H(a)+H(b)-S
=3\left[\frac{(a-b)^2}{ab}
+\frac{a-2}{a(a+1)}+\frac{b-2}{b(b+1)}\right]\ge0.
$$

If one part has size two, only its one nondesignated vertex can contribute positively; the sum is at most $phi$ of the opposite part size, hence at most that part's $H$. If a part has size at most one, its designated vertex has degree at most one and every contribution is zero. This proves (II.A.3). ∎

#### II.A.3 A positive pair type is unique and controls the other types

Write

$$
R_{AB}=T_{AB}-H(n_A)-H(n_B)
$$

and cyclically. If $R_AB>0$, Lemma II.A.1 shows that at most one node of $A∪B$ has degree at most one in $K[A,B]$.

Every node of $A∪B$ touching $C$ has such low $AB$ degree: it is either pure toward $C$, or mixed with total degree two. Thus all $AC$ and $BC$ edges meet at most one node of $A∪B$. Those edges form one star, whose leaves in $C$ contribute zero to $T_AC+T_BC$. Consequently

$$
T_{AC}+T_{BC}\le\phi(n_C)\le H(n_C).\tag{II.A.4}
$$

The last inequality holds also for $n_C=0,1,2$, when both sides vanish. In particular $R_AC,R_BC≤0$, so a positive pair type is unique.

When a positive pair type exists, (II.A.4) immediately gives (II.A.2): the two other negative signed weights sum to

$$
2H(n_C)+H(n_A)+H(n_B)-T_{AC}-T_{BC}
\ge H(n_A)+H(n_B)+H(n_C).
$$

#### II.A.4 The pure base case

Assume there are no mixed nodes. Isolated nodes can be omitted initially and reintroduced later. Complete every compatible pair type; this only increases the $T$ values, so only makes (II.A.2) harder. The result is the disjoint union of at most three complete bipartite graphs, one per pair type.

For a complete bipartite graph with positive side sizes $x,y$, put

$$
S(x,y)=x\phi(y)+y\phi(x).
$$

Its excess over the two individual budgets is exactly

$$
S(x,y)-H(x)-H(y)
=\phi(x)+\phi(y)-(x-y)(\phi(x)-\phi(y))
\le2\min\\{\phi(x),\phi(y)\\}.\tag{II.A.5}
$$

The final bound uses integer side sizes: if they differ, their difference has magnitude at least one.

There are two useful merging identities/inequalities. For $x,u≥2$,

$$
H(x+u)-H(x)-H(u)=2\phi(x)+2\phi(u)+\frac6{x+u+1}.\tag{II.A.6}
$$

For all positive $x,u$,

$$
H(x+u)\ge H(x)+H(u)+\phi(x)+\phi(u).\tag{II.A.7}
$$

For $x,u≥2$, (II.A.7) follows from (II.A.6). If $x=1,u≥2$, the difference between its two sides is $3u/[(u+1)(u+2)]$; if $x=u=1$, it is zero.

- With zero or one nonempty pair type, (II.A.2) is immediate by capping that one type at its own two-part budget.
- With two types, write them as $K_{x,y}$ on $AB$ and $K_{u,v}$ on $AC$. If $x,u≥2$, (II.A.5) and (II.A.6) give $T_AB+T_AC≤H(x+u)+H(y)+H(v)$, which proves (II.A.2). If $x=1$, then $T_AB=phi(y)≤H(y)$. Cap the other type by $H(x+u)+H(v)$; again (II.A.2) follows. The case $u=1$ is symmetric.
- With three types, each original part is the union of two positive side sets. Sum (II.A.5), using its weaker bound by $phi(x)+phi(y)$, and apply (II.A.7) at each original part. This gives $T_AB+T_AC+T_BC≤Σ_iH(n_i)$, proving (II.A.2).

Equivalently, in the pure base case we have the following stronger dichotomy: if all $R_ij≤0$, then $ΣT_ij≤ΣH(n_i)$; if one is positive, it is unique and (II.A.4) holds. The implication in the all-nonpositive case remains valid before completing missing edges, because $Σ min(T_ij,H_i+H_j)−ΣH_i$ is coordinatewise nondecreasing in the $T$ values. Thus (II.A.2) for the completion implies (II.A.2) for the original graph, and with no positive $R$ this is exactly $ΣT≤ΣH$.

#### II.A.5 Induction over mixed nodes

We prove the dichotomy stated at the end of §II.A.4. Suppose $v∈A$ is mixed. It has one neighbor in $B$ and one in $C$. Delete $v$, apply induction, and add it back. Let $a$ be the old size of $A$.

The new node contributes zero to every $T$. Each of its two neighbors can increase its contribution by at most $1/4$, because this is the largest increment of $phi$. If $a≤1$, neither increase can be positive: any neighbor with a positive increase would have at least three neighbors in $A$ after insertion. If $a≥2$,

$$
\Delta H_A=1-\frac6{(a+1)(a+2)}\ge\frac12.
$$

Therefore in every case

$$
\Delta T_{AB}+\Delta T_{AC}\le\Delta H_A.\tag{II.A.8}
$$

Each individual affected $R$ can only decrease, and $R_BC$ stays unchanged. No new positive pair type can appear.

If the smaller graph has no positive type, its total $T$ is at most its total $H$, and (II.A.8) preserves this. If its positive type survives insertion, §II.A.3 directly proves the desired dichotomy for the new graph. If a positive type disappears, it must be $AB$ or $AC$; suppose it is $AB$.

In this last case,

$$
\Delta T_{AC}=0.\tag{II.A.9}
$$

Otherwise the $C$ neighbor of $v$ has at least three $A$ neighbors after insertion, hence at least two distinct $A$ neighbors before insertion. Both of those old $A$ nodes touch $C$, so each has $AB$ degree at most one. This contradicts the two-low-vertices lemma because the old $R_AB$ was positive.

In the smaller graph, (II.A.4) gave $T_AC+T_BC≤H_C$. Equation (II.A.9) preserves that bound, while the disappearance of the positive type says $T_AB≤H_A+H_B$. Summing proves $ΣT≤ΣH$ for the new graph.

Deletion of a mixed node preserves the defining graph property and strictly reduces the number of mixed nodes, so the induction terminates at the pure case. Isolated nodes can be reintroduced in the same argument with all $\Delta T=0$: a surviving positive type is handled by §II.A.3, and a disappearing type leaves the other-type bound unchanged. This finishes the graph theorem and proves $\delta_E\ge0$ for every triple $E$. ∎


### II.B. Removal of near-complete blocks

#### II.B.1 A two-certificate lemma for a block with at most one missing triple

Let $A$ have five vertices and $H[A]$ contain at least nine triples. Fix $x\notin A$ and define the external trace

$$
 F_{A,x}=\\{p\in\binom A2:px\in H\\}.
$$

For $p\in F_{A,x}$, let

$$
 N_A(p)=\\{y\in A\setminus p:py\in H\\}.
$$

**Lemma II.B.1.** There are pairwise disjoint two-element sets $Y_p\subseteq N_A(p)$, one for each $p\in F_{A,x}$.

**Proof.** If $H[A]$ is complete, $F_{A,x}$ has at most one pair: two different pairs $p,q$ would give the two distinct decompositions

$$
 (px,A\setminus p),\qquad(qx,A\setminus q)
$$

of $A\cup\\{x\\}$ into two disjoint triples. Also $|N_A(p)|=3$.

Suppose the unique missing triple is $M$ and put $q=A\setminus M$. Every pair $p\ne q$ has $A\setminus p\in H$. The same decomposition argument shows that at most one such pair belongs to $F_{A,x}$. Thus $|F_{A,x}|\le2$, and if it is two then $F_{A,x}=\\{q,p\\}$ for $p\ne q$. We have $N_A(q)=M$. If $p$ intersects $q$ in one vertex, then $N_A(p)=A\setminus p$ and $|N_A(q)\cup N_A(p)|=4$. If $p$ is disjoint from $q$, then $p\subseteq M$ and $N_A(p)=q$, so the union has size five. Each neighborhood has at least two points and their union has at least four. If either has size two, allocate those two points first. Otherwise, if one has at least four, allocate two points from the other first. In the remaining case both have size three; choose one point belonging only to the first and one further point from it, leaving two for the second. ∎

#### II.B.2 Simultaneous removal of all nine- or ten-triple blocks

**Elementary block linearity.** Distinct five-element sets $A,D$ spanning at least nine triples intersect in at most one vertex. If they intersect in exactly two vertices $x,y$, internal witnesses for $J_{xy}$ in their disjoint remaining three-sets are disjoint. If their intersection has three vertices, choose $x,y$ in that intersection with the same membership in the at-most-one missing triple of $A$ (possible by the pigeonhole principle; if $A$ is complete choose any pair). Then $J_{xy}$ contains the full triangle on $A\setminus\\{x,y\\}$. Every internal witness from $D$ meets its vertex set in at most one vertex, hence is disjoint from some edge of that triangle. If the intersection has four vertices $Q$, let $a,d$ be the respective outside vertices. Both the $a$- and $d$-links on $Q$ have at least five of its six pairs; their intersection gives at least four edges in $J_{ad}$ on four vertices, impossible for an intersecting graph. These exclude all possible nontrivial intersections. Also, every pair inside such a block has at least two internal common-link witnesses, since one missing triple deletes at most one of the three possible witnesses.

Let $B$ be the collection of all five-element sets spanning at least nine triples. By the preceding elementary proof, distinct members of $B$ intersect in at most one vertex. Call a pair covered if it is contained in a member of $B$. Put $b_9=|\\{A\in B:|H[A]|=9\\}|$ and define $b_{10}$ analogously. Every covered pair belongs to a unique block.

A triple not contained in a block is of type $R_i$ if it contains exactly $i$ covered pairs, and $R_i$ also denotes their number. Delete every triple containing a covered pair, and call the remainder $H_0$. The number of deleted triples is

$$
 9b_9+10b_{10}+R_1+R_2+R_3.
$$

**Theorem II.B.2 (arbitrary-degree near-complete-block removal).**

$$
 \boxed{\Psi(H_0)-\Psi(H)\ge 2b_9+R_3\ge0.}
$$

Consequently the universal support inequality is equivalent to its restriction to admissible systems with no five-element set spanning nine or ten triples.

**Proof.** For every incidence consisting of a secondary triple $E=px$ and a block $A$ covering $p$, use Lemma II.B.1 to choose two distinct $y\in N_A(p)$. Record the oriented certificates

$$
 (y,x;p,A,E).
$$

For each fixed $(A,x)$, all chosen $y$ are different, even when $x$ completes two pairs of $A$.

No ordered pair $(y,x)$ occurs for certificates from different blocks. Otherwise $A\cap A'=\\{y\\}$, and the corresponding witness pairs $p\subseteq A\setminus\\{y\\}$ and $p'\subseteq A'\setminus\\{y\\}$ are disjoint, contradicting the intersectingness of $J_{yx}$. Thus every orientation occurs at most once.

Every certificate pair $yx$ is uncovered. Indeed, if $yx$ lay in another block $D$, linearity gives $A\cap D=\\{y\\}$; the internal common-link witness for $yx$ in $D$ is disjoint from $p$, again a contradiction.

If an unordered certificate pair $yx$ occurs in both orientations, write the two certificates as $(y,x;p,A,E)$ and $(x,y;q,D,F)$. Their cores must intersect, because both are edges of $J_{xy}$. The blocks are different and linear, so $p\cap q=\\{a\\}$, where $A\cap D=\\{a\\}$. Hence $E=p+x$ contains the additional covered pair $ax\subseteq D$ and $F=q+y$ contains the additional covered pair $ay\subseteq A$. Both generating triples therefore have type at least two.

It follows that the $2R_1$ certificates generated by $R_1$ triples give distinct unordered pairs which occur nowhere else. The $4R_2+6R_3$ other certificates have multiplicity at most two. If $\Gamma$ is the set of unordered certificate pairs, then

$$
 |\Gamma|\ge 2R_1+2R_2+3R_3. \tag{II.B.1}
$$

Every $\Gamma$-pair disappears from $C$ after the removal. To see this, let $yx$ have core $p=\\{u,v\\}\subseteq A\setminus\\{y\\}$. Any $q\in J_{yx}$ intersects $p$. If $u\in q$, then the witnessing triple $yq$ contains covered pair $yu\subseteq A$ and is deleted; if $v\in q$ the same follows from covered pair $yv$. Thus no witness survives.

All $10(b_9+b_{10})$ covered pairs disappear from $P$. They also disappear from $C$: a covered pair $xy\subseteq A$ has an internal witness $p\subseteq A\setminus\\{x,y\\}$. A surviving witness $q$ for $xy$ would have to avoid $A$, because otherwise $xq$ contains a covered pair and is deleted. But $q$ would then be disjoint from $p$, violating admissibility.

Covered $C$-pairs and $\Gamma$ are disjoint. Thus the total support loss is at least

$$
 20(b_9+b_{10})+2R_1+2R_2+3R_3.
$$

Subtracting twice the number of removed triples proves the displayed inequality. ∎

### II.C. Nonduplication of bridge demands

The source charges and demands are those of §II.6.

**Theorem II.C.1 (bridge demands do not overlap after near-complete removal).** Suppose no five-element set of $H$ spans nine or ten triples. For every triple $E\in H$ there is at most one triangular-reciprocal receiving pair $q\subseteq E$ for which $\gamma(q,E)>0$. Consequently

$$
 \Xi\le\sum_{E\in H}\gamma_E,
$$

where $\gamma_E$ is the unique positive bridge demand if it exists, and zero otherwise. No bridge is counted twice in this sum.

**Proof.** Suppose the contrary. Rename the triple $E=abc$ and two receiving pairs as $ab$ and $ac$. There are vertices $x,u$ outside $\\{a,b,c\\}$, with $x\ne u$, such that

$$
 J_{ab}=\\{xc,xu\\},\qquad J_{cu}=\\{ab,ax,bx\\}.
$$

There are likewise vertices $y,v$ outside $\\{a,b,c\\}$, with $y\ne v$, such that

$$
 J_{ac}=\\{yb,yv\\},\qquad J_{bv}=\\{ac,ay,cy\\}.
$$

Positive demand at $E$ for the first receiver implies $w_b(xc)>0$; positive demand at $E$ for the second implies $w_c(yb)>0$.

First suppose $x\ne y$. In the graph $G_b$, edge $xc$ has the adjacent edge $xu$, with

$$
 \mu_{G_b}(c,u)=2,
$$

because $J_{cu}$ is the displayed triangle and exactly two of its edges contain $b$. The second book supplies edge $cy$ in $G_b$, since $bcy\in H$. This is a different adjacent edge of $xc$; its opposite-endpoint common-neighbor count is $\mu_{G_b}(x,y)$. Positive-edge weak protection therefore forces this count to be at least four. Thus $J_{xy}$ contains a star centered at $b$ with at least four edges, and intersectingness makes $b$ its unique center.

Symmetrically, in $G_c$, edge $yb$ has the mandatory weak alternative $yv$ with $\mu_{G_c}(b,v)=2$; the first book supplies the different alternative $bx$. The positivity of $w_c(yb)$ forces $\mu_{G_c}(x,y)\ge4$, making $c$ the unique center of the same $J_{xy}$. Since $b\ne c$ this is impossible. This argument allows coincidences $u=y$ or $v=x$; the two alternative edges remain distinct.

It remains that $x=y$. The two books imply that $bc,bu,cv$ all belong to $J_{ax}$. If $u\ne v$, the latter two edges are disjoint, so admissibility forces $u=v$. The books now have the same five vertices $\\{a,b,c,x,u\\}$. Their union consists of the nine distinct triples

$$
 abc,\ abu,\ acx,\ axu,\ bcx,\ bxu,\ acu,\ abx,\ cxu.
$$

This contradicts the hypothesis excluding nine-triple blocks. Hence two positive demands cannot share E. Summing (II.10) proves the claimed inequality. ∎


### II.D. Marked-node inequality and bridge payment

#### II.D.1 A marked mixed-node surplus

For a tripartite auxiliary graph, define its signed surplus

$$
\delta(K)=\sum_{ij}[H(n_i)+H(n_j)-T_{ij}]_{+}-\sum_iH(n_i).
$$

§II.A proves $\delta(K)\ge0$.

**Lemma II.D.1 (marked mixed node).** Suppose $x\in A$ is mixed, with neighbors $y\in B,z\in C$. Assume $d_K(y)=r\ge3$, $d_K(z)=s\ge3$, and

$$
N_K(y)\cap N_K(z)=\\{x\\}.
$$

Then

$$
\boxed{\delta(K)\ge\min\\{\phi(r),\phi(s)\\}.}\tag{II.D.1}
$$

**Proof.** Both $y,z$ are pure toward $A$, because their degrees exceed two. Their $A$-neighbor sets have union of size $r+s-1$, so $a=|A|\ge r+s-1$.

In both $K$ and $K-x$, all three pair-type signed weights are nonpositive. For $AB$, the at least two neighbors of $z$ other than $x$ are $A$ nodes touching $C$, so have $AB$ degree at most one. For $AC$, use the at least two other neighbors of $y$. For $BC$, the two nodes $y,z$ have degree zero. Apply the two-low-vertices lemma in all three cases.

Consequently, in these two graphs $\delta=\sum H-\sum T$, with no positive-part ambiguity. Deleting $x$ affects only the contributions of $y,z$ and the size of $A$. Since $a\ge5$,

$$
\begin{aligned}
\delta(K)
&=\delta(K-x)+1-\frac6{a(a+1)}
-\frac3{r(r+1)}-\frac3{s(s+1)}\\
&\ge1-\frac6{a(a+1)}-\frac3{r(r+1)}-\frac3{s(s+1)}.
\end{aligned}
$$

Assume $r\le s$. Subtracting $\phi(r)$ and using $a\ge r+s-1\ge2r-1$ gives a lower bound

$$
\frac{3(r-2)}{r(r+1)}-\frac6{(2r-1)(2r)}>0.
$$

The last strict inequality is equivalent to

$$
(r-2)(2r-1)>r+1,
$$

whose difference is $2r(r-3)+1>0$ for $r\ge3$. This proves (II.D.1), in fact with strict slack. ∎

##### Exact bridge interpretation

Suppose a receiving common link and its reciprocal are

$$
J_{at}=\\{bc,bx\\},\qquad J_{cx}=\\{ab,at,bt\\}.
$$

Consider the bridge triple $E=act$. Use its auxiliary parts

$$
A=N(at)\setminus\\{c\\},\quad
B=N(ac)\setminus\\{t\\},\quad
C=N(ct)\setminus\\{a\\}.
$$

The node $A_x$ is mixed, adjacent to $B_b,C_b$. If both their degrees are at least three, they are pure toward $A$. Their common $A$ neighbors correspond exactly to edges $bu$ of $J_{at}$, other than its edge $bc$ already represented by the central triple. Since $J_{at}=\\{bc,bx\\}$, their common-neighbor set is exactly $\\{A_x\\}$.

Here $c(bt)=1+d_K(B_b)$: the common link $J_{bt}$ contains $ac$, and each of its other edges must contain $a$ or $c$. Those other edges correspond bijectively to neighbors of $B_b$ in $A$ or $C$, respectively. The analogous identity holds for $C_b$ and $J_{ab}$. Thus the full auxiliary degree is used before any assertion of purity.

The positive directed source weights obey

$$
(w_a(bc))_{+}\le\phi(d_K(B_b)),\qquad
(w_t(bc))_{+}\le\phi(d_K(C_b)).\tag{II.D.2}
$$

For the first inequality, the two mandatory alternatives in $G_a$ are $bx$ and $ct$. The first has common-neighbor count two. The second has common-neighbor count at most $c(bt)=1+d_K(B_b)$. In the nonnegative-deficit expression for $w_a(bc)$, the positive base is at most the sum of the two endpoint $f$ values; subtracting these two alternatives leaves at most $g(1+d_K(B_b))=\phi(d_K(B_b))$, by monotonicity of $g$. The other inequality is symmetric. This argument is also valid when the source weight is nonpositive.

Define the actual directed contributions

$$
\alpha_c=\frac{(w_a(bc))_{+}}{d(bc)-1},\qquad
\beta_c=\frac{(w_t(bc))_{+}}{d(bc)-1}.
$$

The denominator is at least one. If both are positive, (II.D.2) implies both marked-neighbor degrees are at least three. The marked lemma therefore yields

$$
\boxed{\delta(act)\ge\min\\{\alpha_c,\beta_c\\}.}\tag{II.D.3}
$$

If either contribution is zero, (II.D.3) follows from the unmarked theorem. The other bridge $atx$ satisfies the symmetric inequality for the core edge $bx$.

The nonduplication theorem of §II.C assigns at most one positive bridge demand to each triple. Summing (II.D.3) therefore gives $\Xi\le\sum_E\delta_E$.


## III. Rank four: controlled preprocessing and a finite deficit

The proof separates star layers from an outside remainder, and measures how that remainder spends the star layers' pair budget. Its fixed-parent labels and edge-deletion costs are needed for the exact branch, so the preprocessing proof is given before the deficit theorem.

### III.A. Preprocessing with actual edge loss


All families are admissible, all degrees count actual edges, and the ambient parameter $n$ remains fixed during deletions. Isolated vertices may be retained. Constants in $O(\cdot)$ are independent of $n$; dependence on fixed parameters is indicated.

#### III.A.1 Elementary consequences of admissibility

For distinct vertices $a,b$, the common triple family $J_{ab}$ is intersecting: disjoint members $T,T'$ would give the forbidden pairs $\\{aT,bT'\\}$ and $\\{bT,aT'\\}$.

An intersecting triple family with maximum pair degree $D$ has at most $\max(Du/2,9D)$ members on at most $u+1$ vertices. If it has a common point, count the opposite-pair graph of maximum degree $D$. Otherwise fix one member $T$, and for each $x\in T$ choose a member avoiding $x$. Every member contains one of the resulting at most nine pairs. An intersecting ordinary graph is a star or a triangle, so with maximum degree $D$ it has at most $\max(D,3)$ edges.

The same trade shows that, for disjoint pair roots $P,Q$, their common pair-tail family is an intersecting graph. We use these facts repeatedly.

#### III.A.2 Separating star layers

Let $z_1,\ldots,z_h$ lie outside a common ground set $U$, $u=|U|$, and put $L_i=\\{T\subseteq U:|T|=3,\ z_iT\in H\\}$. For $P\in\binom U2$, write $d_i(P)=|\\{x:Px\in L_i\\}|$. For $i\ne j$,

$$
\sum_Pd_i(P)d_j(P)=O(u^3). \tag{III.A.18}
$$

Equal completions contribute $3|L_i\cap L_j|=O(u^2)$, since the intersection is an intersecting triple family and is covered by the three stars through a fixed member. For distinct completions $x,y$, the corresponding pairs $P$ form an intersecting graph on $U\setminus\\{x,y\\}$, with at most $u-3$ edges for $u\ge6$. This proves (III.A.18).

Assign each pair to an index maximizing $d_i(P)$; delete every colored triple containing a pair assigned elsewhere. The surviving pair shadows are disjoint. If $s_P$ is the sum of the nonmaximal entries at $P$, then

$$
s_P^2\le2\sum_{i<j}d_i(P)d_j(P).
$$

Cauchy and (III.A.18) bound the total deletion cost by $O(hu^{5/2})$.

If $M_1$ bounds the original link sizes, the surviving links $L_i'$ obey

$$
\sum_i|L_i'|\le \frac{u^2}{6}(6M_1)^{1/3}. \tag{III.A.19}
$$

This follows from the shadow-power inequality proved in Lemma IV.3.1: for a triple family $\mathcal T$ with pair shadow $\partial_2\mathcal T$,
$(6|\mathcal T|)^2\le(2|\partial_2\mathcal T|)^3$.
Apply it to each surviving link $L_i'$. Their pair shadows are disjoint, so with $x_i=6|L_i'|/u^3$,

$$
\sum_i x_i^{2/3}\le\frac{2}{u^2}\sum_i|\partial_2L_i'|
\le\frac{2\binom u2}{u^2}\le1.
$$

Since $\sum_i x_i\le(\max_i x_i)^{1/3}\sum_i x_i^{2/3}$, this proves the displayed allocation bound.

#### III.A.3 The fixed decomposition

The finite coarse bound $|H|\le32n^3$ in §I.1 suffices here. Remove the vertices $Z$ of degree greater than $n^{27/10}$; there are $O(n^{3/10})$.

In $H-Z$, triples of degree at least $t=\lceil n^{3/5}\rceil$ have a vertex cover $X$ of size $O(n^{2/5})$. Indeed, choose a matching of $k$ such triples and $t$ completions for each. Two selected completion sets meet in at most one vertex, by admissibility. Counting their vertex multiplicities gives

$$
k^2t^2\le n(kt+k(k-1)),\qquad
k\le\frac{n(t-1)}{t^2-n}.
$$

The vertices of a maximal matching cover all heavy triples.

Set $U=V(H)\setminus(Z\cup X)$, $B=H[U]$. Then $u=n-O(n^{2/5})$, $\Delta_1(B)\le n^{27/10}$, and $\Delta_3(B)<t$. Edges meeting $Z\cup X$ at least twice cost $O(n^{14/5})$. For edges meeting it only at a center in $X$, §III.A.2 with $M_1=n^{27/10}$ bounds the entire layer by

$$
O(|X|n^{5/2})+\frac{n^2}{6}(6n^{27/10})^{1/3}
=O(n^{29/10}).
$$

Clean the links at centers in $Z$ by §III.A.2, losing $O(n^{14/5})$, and call the surviving links $A_c$. Their pair shadows are disjoint and

$$
|H|\le |B|+\sum_c|A_c|+O(n^{29/10}).
$$

For each $c\in Z,y\in U$, the family $\\{T\in A_c:yT\in B\\}$ is intersecting, with maximum pair degree at most $t$. §III.A.1 bounds its size by $O(tn)$. Summing over $c,y$ gives

$$
|A\cap\partial_3B|\le O(|Z|tn^2)=O(n^{29/10}).
$$

This establishes (III.B.1), using only original star edges.

#### III.A.4 Regularization with arbitrarily small edge loss

We prove a uniform one-step contraction. If

$$
|F|\le32n^3,\quad
\Delta_j(F)\le Rn^{3-j}\ (j=1,2,3),\quad
R_{\ast}\le R\le n^{8/11},
$$

then a subfamily $F'$ satisfies

$$
|F\setminus F'|\le C R^{-1/8}n^3,\qquad
\Delta_j(F')\le R^{3/4}n^{3-j}. \tag{III.A.20}
$$

Here $C,R_{\ast}$ are absolute constants.

Put $T=R^{5/8}$. Cover vertices of degree greater than $Tn^2$ and pairs of degree greater than $Tn$ by a set $X$ of size $O(n/T)$. The vertex count is at most $4|F|/(Tn^2)\le128n/T$, as required. For the pairs, take a maximal matching of $k$ heavy roots. Their pair-tail families have pairwise intersections of size at most $R$, by §III.A.1. Selecting $d=\lfloor Tn\rfloor+1$ tails per root and counting multiplicities on at most $n^2$ pairs gives

$$
k^2d^2\le n^2(kd+k(k-1)R),\qquad
k\le\frac{n^2(d-R)}{d^2-n^2R}\le4n/T
$$

for sufficiently large fixed $R_{\ast}$. The maximal matching covers the heavy pairs.

Edges meeting $X$ at least twice cost $O(R/T^2)n^3$. For the exactly-once layer, (III.A.18) improves to $O(Rn^2)$: its distinct-completion intersecting graphs have maximum degree at most $R$, and the equal-completion contribution is $O(Rn)$. The same pair-owner cleaning therefore costs $O(|X|\sqrt R\\,n^2)=O(R^{-1/8})n^3$. By (III.A.19), the remaining exactly-once layer is at most

$$
\frac{n^2}{6}(6Rn^2)^{1/3}=O(R^{-1/8})n^3,
$$

where the last inequality is exactly the restriction $R\le n^{8/11}$.

Delete the entire layer touching $X$. The induced remainder $F_0$ has $\Delta_1\le Tn^2$, $\Delta_2\le Tn$, and $\Delta_3\le R$. Each common triple cell has size at most $9Tn$: a common point gives a bound $Tn$ using the pair degree, and the no-common-point case gives $9R\le9Tn$. Hence

$$
\sum_P\binom{d_{F_0}(P)}2=\sum_{a<b}|J_{ab}(F_0)|
\le(9/2)Tn^3.
$$

Delete every edge containing a triple of degree greater than $R^{3/4}$. Their number is at most $18R^{-1/8}n^3$. This proves (III.A.20).

The initial $B$ from §III.A.3 has natural degree factor $R_0=n^{7/10}$, since
$2d_B(P)=\sum_{x\notin P}d_B(Px)$. Iterate (III.A.20), replacing $R$ by $R^{3/4}$, until the factor is at most a fixed $L$. All inputs are in range. The total loss divided by $n^3$ is at most

$$
C\sum_{j\ge0}L^{-(4/3)^j/8}
\le\frac{C L^{-1/8}}{1-L^{-1/24}}.
$$

Choosing $L$ large enough makes this at most any prescribed $\rho>0$, proving (III.B.2).

#### III.A.5 A bounded-label separation lemma

**Lemma III.A.1 (bounded-label separation).** Let a four-family $F$ have $\Delta_3(F)\le D$, and let a triple system $\mathcal Q$ have maximum pair degree at most $\kappa$. For fixed $D,\kappa$, one can delete $O_{D,\kappa}(n^{5/2})$ edges so that, for each remaining edge $E$, the six sets

$$
C_{\mathcal Q}(P)=\\{x:Px\in\mathcal Q\\},\qquad P\in\binom E2,
$$

are pairwise disjoint and each is disjoint from $E$.

**Proof.** For each $x$, let $F_x$ be its link graph in $\mathcal Q$, of maximum degree $\kappa$. Edges of the four-family containing an internal triple $xab\in\mathcal Q$ cost $O(D\kappa n^2)$. Two intersecting pair cores $ab,ac\in F_x$ cost $O(D\kappa^2n^2)$, by counting wedges and then completions of the fixed triple $abc$.

For disjoint cores, form a graph on the pair-nodes of $F_x$, joining $P,Q$ if they are disjoint and $P\cup Q\in F$. Greedily color the edges of $F_x$ with $c_\kappa=2\kappa-1$ colors: each edge meets at most $2\kappa-2$ previously colored edges. Each color class is a matching. Between any two color classes the bipartite graph is $C_4$-free: a rectangle has disjoint rows, disjoint columns, and disjoint cross pairs, so its four physical pairs are mutually disjoint and give a forbidden trade. This also covers a color class paired with itself, since a repeated physical pair-node would require a loop.

A $C_4$-free bipartite graph with parts $S,T$, of sizes $s,t$, and $e$ edges satisfies $\sum_{v\in T}\binom{d(v)}2\le\binom s2$. Cauchy gives $e^2/t-e\le s(s-1)$, hence $e\le s\sqrt t+t$; the case $t=0$ is immediate. If $N_x=e(F_x)$ and the color classes have sizes $N_i$, summing over ordered color pairs gives

$$
2e(\text{pair-node graph})
\le N_x\sum_i\sqrt{N_i}+rN_x
\le\sqrt{c_\kappa}\\,N_x^{3/2}+c_\kappa N_x.
$$

Since $N_x=O_\kappa(n)$, summing over $x$ costs $O_\kappa(n^{5/2})$. Delete all four-edges so represented, together with the earlier exceptions. ∎

#### III.A.6 Classification and isolated reciprocals

Start with $B_1$ from §III.A.4, fix $\alpha>0$, and put

$$
D=\max(2,\lceil L_\rho\rceil),\qquad t=\lceil\alpha n\rceil.
$$

Repeatedly clear every nonempty cell $J_{ab}$ of size less than $t$, deleting its two endpoint edges per member. A cleared pair stays empty, so the total cost is at most
$2(t-1)\binom u2\le\alpha n^3$. Call the result $B_0$.

Every nonempty cell of $B_0$ is intersecting with maximum pair degree $D$. For large $n$, $t>9D$, so §III.A.1 gives a unique common point $\ell(ab)$; two common points would bound the cell size by $D$. The native graph has at least $t$ edges and maximum degree $D$, hence a matching of at least $t/(2D-1)$ tails, eventually at least three.

The center graphs $\Gamma_z=\\{ab:\ell(ab)=z\\}$ have maximum degree at most

$$
K_{\ast}=\max(1,\lceil(D-1)L_\rho/\alpha\rceil).
$$

Indeed $t\\,d_{\Gamma_z}(a)\le(D-1)d_{B_0}(az)$: each edge through $az$ is counted for at most $D-1$ other completions of its opposite facet. The symmetric system
$\mathcal Q=\\{ab\ell(ab)\\}$ thus has maximum pair degree at most $2K_{\ast}+1$.

All labels and witnesses in the next deletions are measured in this fixed parent $B_0$.

First delete every edge through a facet with a completion triangle using exactly two colors. Such a triangle has a repeated-color wedge. There are $O(K_{\ast}^2n^2)$ wedges; the two distinct labels and one fixed completion leave at most $D$ possible supporting facets, each in at most $D$ edges. The cost is $O(D^2K_{\ast}^2n^2)$.

A clique colored in at most three colors with no exactly-two-color triangle is monochromatic, a rainbow triangle, or a proper $K_4$. A monochromatic triangle forces every further vertex to join it in its color: otherwise its three incident edges would have to use three colors other than that color. Then edges between further vertices have that color too. In the absence of monochromatic triangles every triangle is rainbow, so the clique has order at most four. These possibilities are hereditary; private facets are permitted.

Next consider a reciprocal $a\leftrightarrow b$ in $E=abP$, with witnesses

$$
\ell(ax)=b,\quad\ell(by)=a,\quad bxP,ayP\in B_0.
$$

There are at most $K_{\ast}$ choices each for $x,y$ at a fixed $ab$. If $x\ne y$, the disjoint pair roots $bx,ay$ have at most $\max(D,3)$ common tails by §III.A.1. Delete every such $E$, at cost $O_D(K_{\ast}^2n^2)$.

If $x=y=w\ne\ell(ab)$, the edges $awP,bwP$ show that $\ell(ab)\in wP$, hence $\ell(ab)\in P$. There are at most $D$ edges containing the fixed triple $ab\ell(ab)$, and at most $K_{\ast}$ choices for $w$. Delete these at cost $O(DK_{\ast}n^2)$. Every surviving reciprocal now has one common witness $w=\ell(ab)$ and

$$
\ell(aw)=b,\qquad\ell(bw)=a,\qquad\ell(ab)=w.
$$

Multiple witnesses would include a distinct-witness choice already deleted.

Finally apply §III.A.5 to the parent $B_0,\mathcal Q$, and delete its exceptional edges. Take the union of all deletions to obtain $K$. The additional cost after weak-cell clearing is $O_{\rho,\alpha}(n^{5/2})$.

To verify the reciprocal condition, a surviving reciprocal has three edges $Pab,Paw,Pbw$. Suppose the ordinary pair-link triangle at $P$ has an attachment $Pat$, $t\notin\\{a,b,w\\}$. The completion triangle $b,w,t$ at $Pa$ is monochromatic or rainbow. In the first case, $\ell(bt)=a$ is a second reciprocal witness in $Pab$, impossible. In the second, writing $P=pq$, its other two labels are $p,q$; after interchanging their names, $\ell(bt)=p,\ell(wt)=q$. Then

$$
t\in C_{\mathcal Q}(pb)\cap C_{\mathcal Q}(qw)
$$

for the actual edge $Pbw$, contradicting separation. The same argument holds at $b,w$. Thus the triangle is an entire component; its three facets have degree two and are monochromatic.

All labels remain valid under deletion. The strong matching witnesses in $B_0$ remain original $H$-edges and give (III.B.4), even when absent from $K$. The total loss proves (III.B.3).


### III.B. One budget for stars and native graphs

The families and labels in the following theorem are those constructed in §III.A. The same finite deficit controls both the leading asymptotic and the stability statement.


**Theorem III.1 (rank-four stability and exactness).** As $n\to\infty$,

$$
g_4(n)=(1+o(1))\binom n3.
$$

Moreover, every admissible sequence with at least $(1-o(1))\binom n3$ edges has a vertex in $(1-o(1))\binom n3$ edges. Consequently, for all sufficiently large $n$,

$$
g_4(n)=\binom{n-1}3+\left\lfloor\frac{n-1}4\right\rfloor.
$$

The eventual equality families are the two constructions in §III.B.6.

**Proof of Theorem III.1.** We first record the reductions of §III.A, then derive the finite deficit and apply Theorem III.2.

#### III.B.1 The preprocessing interface

Write $N_u=\binom u3$, and call an occurring triple a *facet*. Its degree is its number of edge completions; it is private when that degree is one.

Section III.A supplies a set $U$, $u=n-O(n^{2/5})$, an induced remainder $B=H[U]$, and triple families $A_c\subseteq\binom U3$ with centers $c\notin U$. Put $A=\bigcup_c A_c$, $a=|A|$. Then

$$
\begin{gathered}
cT\in H\quad(T\in A_c),\qquad
\partial_2 A_c\text{ are pairwise disjoint},\\
|H|\le a+|B|+O(n^{29/10}),\qquad
|A\cap\partial_3B|=O(n^{29/10}),\\
\Delta_1(B)\le n^{27/10},\qquad
\Delta_3(B)<\lceil n^{3/5}\rceil.
\end{gathered}\tag{III.B.1}
$$

The decomposition is fixed independently of all subsequent error parameters.

For every fixed $\rho>0$, $B$ has a subfamily $B_1$ losing at most $\rho n^3$ edges and satisfying

$$
\Delta_j(B_1)\le L_\rho n^{3-j}\quad(j=1,2,3). \tag{III.B.2}
$$

For every fixed $\alpha>0$, a further cleanup gives $K\subseteq B_1$, with

$$
|B\setminus K|\le(\rho+\alpha)n^3+o_{\rho,\alpha}(n^3). \tag{III.B.3}
$$

Here is the precise finite structure of $K$. For each used completion pair $ab$, all triples in

$$
J_{ab}(K)=\\{T:aT,bT\in K\\}
$$

contain a fixed label $z=\ell(ab)\notin\\{a,b\\}$. Write $J_{ab}=z+G_{ab}$, where $G_{ab}$ is counted on its nonisolated vertices, and put

$$
V=\sum_{ab}|V(G_{ab})|.
$$

The completion clique of every nonprivate facet, colored by these labels, is monochromatic, a rainbow triangle, or a properly three-edge-colored $K_4$. For $i,j\in E\in K$, write $i\to j$ if $\ell(ix)=j$ for another completion $x$ of $E-i$. Every reciprocal pair $i\leftrightarrow j$ has two monochromatic opposite facets of degree two.

Finally, each used $ab$ has a matching of at least three tails $P$ with

$$
azP,bzP\in H,\qquad z=\ell(ab).
\tag{III.B.4}
$$

These witnesses are in a fixed parent of $K$; they are not required to survive in $K$.

#### III.B.2 One graph lemma

**Lemma III.B.1 (graph potential).** For a graph $F$, let $q(F)$ count unordered vertex pairs with a common neighbor, $U(F)$ those with exactly one, and $v(F)$ its number of nonisolated vertices. Set

$$
\mathcal L(F)=q(F)-e(F)+v(F)/2.
$$

Then $\mathcal L(F)\ge0$. More precisely, mark any vertices of degree three or four such that every pair containing a marked vertex has at most two common neighbors. If $M_3,M_4$ count the marked vertices of the respective degrees, then

$$
\mathcal L(F)\ge U(F)/2+M_3/2+M_4. \tag{III.B.5}
$$

**Proof.** For a nonisolated vertex $x$, write $d_x=d_F(x)$,

$$
A_x=\sum_{y\in N(x)}d_y,\qquad
S_x=\sum_{y\ne x}\min(2,|N(x)\cap N(y)|).
$$

For $d_x\ge2$, put $D_x=S_x-2A_x/d_x+2\ge0$. This follows from
$\min(2,\mu)\ge2\mu/d_x$ and $\sum_{y\ne x}\mu_{xy}=A_x-d_x$.
Direct summation gives

$$
\mathcal L(F)-U(F)/2
=\frac14\sum_{d_x\ge2}D_x
+\frac12\sum_{xy\in E(F)}
 \left(\frac{d_x}{d_y}+\frac{d_y}{d_x}-2\right)
-\frac14\sum_{d_x=1}(d_{N(x)}-1). \tag{III.B.6}
$$

A leaf edge to a vertex of degree $k$ has ratio term minus leaf subtraction
$(k-1)(k-2)/(4k)\ge0$.

At a marked vertex the common-neighbor assumption gives

$$
D_x=(1-2/d_x)A_x-d_x+2.
$$

Discard the nonnegative $D_x$'s at other vertices. On an edge from a marked vertex of degree $d$ to an unmarked nonleaf of degree $k$, allocate the whole ratio term to the marked endpoint. Together with that endpoint's $D_x/4$ contribution this is

$$
k/4+d/(2k)-1.
$$

For $d=3$ it is at least $1/4$; for $d=4$ it is at least $3/8$. The first bound is equivalent to $(k-2)(k-3)\ge0$, and the second to $2k^2-11k+16>0$. Leaf neighbors give $1/4$ and $1/2$, respectively.

On a marked--marked edge, use only each endpoint's own $D_x/4$ contribution: it is $k/12$ at degree three and $k/8$ at degree four. Since $k\in\\{3,4\\}$, these are at least $1/4$ and $3/8$, respectively. Discard the ratio term. Thus no special allocation is needed on an edge joining degrees $3$ and $4$.

Subtracting the constant $(d-2)/4$ at each marked vertex leaves $1/2$ for degree three and $1$ for degree four. Edges between unmarked vertices have nonnegative remaining contributions by the leaf calculation. This proves (III.B.5), and also the unmarked assertion. ∎

#### III.B.3 The finite deficit lemma

**Lemma III.B.2 (finite deficit).** Suppose $K$ has the finite labeling, classification, and reciprocal properties in §III.B.1. Write

$$
m=|K|,\quad s=|\partial_3K|,\quad
b=\\#\\{\text{nonprivate facets}\\},\quad
m_0=\\#\\{\text{edges with four private facets}\\}.
$$

Then the single estimate needed for both asymptotics and stability is

$$
\boxed{S:=V+2s-5m\ \ge\ b/2+3m_0.} \tag{III.B.7}
$$

**Proof.**

**Selected pair links.** For each pair $Q$, take the ordinary pair link induced on vertices $x$ such that $Qx$ is nonprivate and either colored, or monochromatic with its center in $Q$. Call it $F_Q$. A monochromatic facet offers two eligible slots $(Q,x)$, a colored facet three, and a private facet none. A slot has selected degree $k=d_{F_Q}(x)$, possibly zero, and full facet degree $d\ge2$.

Set

$$
e_{\ast}=\sum_Qe(F_Q),\quad
W=\sum_Q\sum_x\binom{d_{F_Q}(x)}2,\quad
R_3=\sum_T\binom{d_K(T)}2.
$$

The exact native representation is

$$
V=2R_3-W+\sum_Qq(F_Q). \tag{III.B.8}
$$

Here is the full incidence explanation. By the degree-sum identity, $W=\sum_Q\sum_{a<b}\mu_{ab}(F_Q)$, while $\sum_Qq(F_Q)=\sum_Q\sum_{a<b}\mathbf1_{\\{\mu_{ab}(F_Q)>0\\}}$. Thus $W-\sum_Qq(F_Q)$ counts $\sum\max(\mu-1,0)$ over all $(Q,ab)$. A pair $ab$ with a common neighbor in $F_Q$ is a used completion pair and has its fixed label $z=\ell(ab)$. If $z\notin Q$, each common neighbor $x$ would give $Qx\in J_{ab}$, hence $z\in Qx$; therefore $x=z$ and $\mu\le1$, contributing zero.

If $z\in Q$, write $Q=\\{z,w\\}$. The common neighbors of $a,b$ in $F_Q$ correspond to edges at the native vertex $w$ of $G_{ab}$. If $w$ has at least two native neighbors, the facets $Q+a$ and $Q+b$ are nonprivate. Choose two distinct native neighbors $x,y$ of $w$. The completion pair $xy$ is supported at both facets $Q+a$ and $Q+b$, so its unique parent label lies in their intersection $Q$. If either facet is monochromatic, its center is this label and lies in $Q$; a colored facet is selected by definition. Thus both endpoint facets are eligible. For any native neighbor $x$, the facet $Q+x$ has completions $a,b$, so is also selected. All native neighbors therefore occur, and $\mu_{ab}(F_Q)=d_{G_{ab}}(w)$. If $w$ has degree one it contributes nothing to $\sum\max(\mu-1,0)$. Consequently

$$
W-\sum_Qq(F_Q)=\sum_{ab}\sum_{w\in V(G_{ab})}(d_{G_{ab}}(w)-1)
=2\sum_{ab}e(G_{ab})-V.
$$

Each edge of $G_{ab}$ represents one pair of completions at one facet, so $\sum_{ab}e(G_{ab})=R_3$. This proves (III.B.8).

**The accounting identity.** Let $r_3,r_4$ count the two colored facet types and $R$ count reciprocal pairs with their containing edges. Define

$$
g_d(0)=(d-\tfrac12)(d-2),\qquad
g_d(k)=(d-k)(d+k-\tfrac52)\quad(1\le k\le d),
$$

and let $G$ be its sum over all eligible slots; every term is nonnegative. Put $\mathcal L=\sum_Q\mathcal L(F_Q)$.

For an edge $E$, let $p_E$ count private opposite facets, $h_E=4-p_E$, $c_E$ colored facets, $l_E$ monochromatic arrows landing at nonprivate rows, and $t_E$ reciprocal pairs. Its number $k_E$ of retained pair-link occurrences is

$$
k_E=\binom{h_E}2-l_E+t_E.
$$

Each monochromatic row excludes its own target pair, and two exclusions coincide precisely at a reciprocal. Define

$$
z_E=2+c_E-k_E+p_E+t_E,\qquad Z=\sum_Ez_E.
$$

These quantities satisfy $z_E\ge0$: for $h_E=4$, $l_E=4-c_E$ and $z_E=0$; for $h_E=3$, $z_E=c_E+l_E$; for $h_E\le2$, $z_E=6-h_E-\binom{h_E}2+c_E+l_E\ge0$. An all-private edge has $z_E=6$, so $Z\ge6m_0$.

Equation (III.B.8) now gives the exact identity

$$
S=b-R/2+Z/2-\frac{11}4r_3-\frac{11}2r_4+G/2+\mathcal L. \tag{III.B.9}
$$

To verify the coefficient identity without an implicit row count, first use $R_3=\frac12\sum_Td(T)(d(T)-1)$, $\sum_Td(T)=4m$, $W=\frac12(\sum k^2-\sum k)$ and $\sum k=2e_{\ast}$. The definition $\mathcal L(F_Q)=q(F_Q)-e(F_Q)+v(F_Q)/2$ then gives

$$
2V=\sum_T\left(2d(T)^2-\sum_{\text{slots at }T}k^2
-\\#\\{\text{positive slots at }T\\}\right)-8m+4e_{\ast}+2\mathcal L.
$$

the facet bracket is $2$ for a private facet,
$5d-2-\tfrac52\sum k+\sum g_d(k)$ for a monochromatic facet,
and $-d^2+\tfrac{15}2d-3-\tfrac52\sum k+\sum g_d(k)$ for a colored facet.
Use $\sum_Td(T)=4m$, $\sum k=2e_{\ast}$, and
$Z=2m+3r_3+4r_4-e_{\ast}+(s-b)+R$ to obtain (III.B.9).

**Colored payment.** In any $F_Q$, a vertex whose facet $Qx$ is colored has common-neighbor multiplicity at most two with every other vertex. Otherwise three common neighbors give a triangle of completion labels all in $Q$, whereas every triangle at the colored facet $Qx$ is rainbow.

Mark the colored slots whose selected degree equals their full degree. By (III.B.5),

$$
\mathcal L\ge U_{\rm tot}/2+M_3/2+M_4. \tag{III.B.10}
$$

For a colored facet $T$, a color $z\in T$, and $Q=T-z$, its completion pairs of color $z$ give one record for a rainbow triangle and two disjoint records for a proper $K_4$. If both endpoints survive as neighbors of $z$ in $F_Q$, their unique common neighbor is $z$. Different records $(Q,ab)$ recover $T=Q+\ell(ab)$, so are distinct. A selected degree $k$ loses at most

$$
\lambda_3(k)=1_{\\{k<3\\}},\qquad
\lambda_4(k)=\min(2,4-k)
$$

records. Consequently

$$
U_{\rm tot}\ge3r_3+6r_4-\sum_{\text{colored slots}}\lambda_d(k).
$$

For $c_3=1/2,c_4=1$, the nine elementary slot inequalities are

$$
\tfrac12 g_d(k)+c_d1_{\\{k=d\\}}-\tfrac12\lambda_d(k)\ge c_d. \tag{III.B.11}
$$

For $d=3$, the values of $g_d(k)/2$ are $5/4,3/2,5/4,0$; for $d=4$, they are $7/2,15/4,7/2,9/4,0$. Thus (III.B.10)--(III.B.11), with three slots per colored facet, imply

$$
\mathcal L+G/2\ge3r_3+6r_4.
$$

Equation (III.B.9) yields $S\ge b-R/2+Z/2$. Each reciprocal uses two monochromatic degree-two facet incidences, each at most once. Hence $R$ is at most the number of degree-two facets, and therefore $R\le b$. Together with $Z\ge6m_0$, this proves (III.B.7). ∎

#### III.B.4 Stars and native graphs share one budget

Let $\mathcal C$ be the used completion pairs of $K$. If $ab\in\mathcal C$ and $aP,bP\in A$, disjointness of the pair shadows forces these triples to have the same original center $c$. We claim

$$
\ell(ab)\in P. \tag{III.B.12}
$$

Otherwise a parent matching of three tails in (III.B.4) contains a tail $R$ disjoint from $P$. The common triples $cP$ and $\ell(ab)R$ are then disjoint members of $J_{ab}(H)$, contradicting admissibility. This is the only use of the parent matchings.

For any graph $F$ on at most $v$ vertices, independent vertex sampling with probability $\theta$, followed by $q\ge e-v/2$, gives

$$
e(F)\le\sum_{a<b}\bigl[1-(1-\theta)^{\mu_{ab}}\bigr]+\frac{v}{2\theta}. \tag{III.B.13}
$$

Both endpoints must be sampled for a pair record; conditional on this, at least one of its $\mu_{ab}$ common neighbors must be sampled. Dividing the expected inequality by $\theta^2$ proves (III.B.13).

Apply this to the graphs $L_x=\\{ab:xab\in A\\}$, and sum over $x\in U$. For a used pair $ab$, (III.B.12) implies $\mu_{ab}(L_x)\le1$ unless $x=\ell(ab)$. Thus this pair contributes at most $1+(u-3)\theta$, while any unused pair contributes at most $u-2$. Writing $c=|\mathcal C|$, we obtain

$$
3a+(u-3)(1-\theta)c\le3N_u+\frac{u(u-1)}{2\theta}.
$$

Every native graph omits its two completion vertices and its label, so $V\le(u-3)c$. Taking $\theta=u^{-1/2}$ gives

$$
3a+V\le3N_u+u^{5/2}. \tag{III.B.14}
$$

Also (III.B.1) gives $a+s\le N_u+O(n^{29/10})$. Combining this with (III.B.7) and (III.B.14) yields the master inequality

$$
\boxed{5(a+m)+b/2+3m_0
\ \le\ 5(a+m)+S
\ \le\ 5N_u+O(n^{29/10}).} \tag{III.B.15}
$$

#### III.B.5 Asymptotics and stability from the same inequality

For fixed $\rho,\alpha>0$, (III.B.1), (III.B.3), and (III.B.15) give

$$
|H|\le\binom n3+(\rho+\alpha)n^3+o_{\rho,\alpha}(n^3).
$$

Letting these fixed parameters be arbitrarily small proves the upper asymptotic. A complete vertex star supplies the lower asymptotic.

For stability, suppose $|H_n|\ge\binom n3-o(n^3)$, and keep the same original decomposition $A,B$. First obtain a uniform degree tail on $B$. For any $\tau>0$, apply (III.B.2) with deletion budget $\tau n^3/8$, and choose $M\ge1$ at least twice its resulting maximum facet degree. Then

$$
\sum_{T:d_B(T)>M}d_B(T)\le
2\sum_T(d_B(T)-d_{B_1}(T))\le\tau n^3. \tag{III.B.16}
$$

The last sum counts each deleted edge four times. The same tail bound holds for every $K\subseteq B$. This auxiliary use of regularization supplies an inequality on $B$; it does not change the later cleanup or its labels.

Now choose $\nu=\rho+\alpha$. Equations (III.B.1), (III.B.3), and (III.B.15) imply

$$
S\le5\nu n^3+o_{\rho,\alpha}(n^3).
$$

Every edge outside the $m_0$ all-private edges contains a nonprivate facet. By (III.B.7) and (III.B.16),

$$
m\le m_0+Mb+\tau n^3\le2MS+\tau n^3.
$$

Hence

$$
|B|/n^3\le(10M+1)\nu+\tau+o_{\rho,\alpha}(1). \tag{III.B.17}
$$

Choose $\tau$ first, then its fixed $M$, then $\nu$, and finally let $n\to\infty$. This proves $|B|=o(n^3)$.

It follows that $a=(1-o(1))u^3/6$. Applying Lemma IV.3.1 to the triangle family in each pair-shadow graph gives

$$
a\le\frac{u^2}{6}\bigl(6\max_c|A_c|\bigr)^{1/3}.
$$

Indeed, (IV.3.1) gives at most $(2e)^{3/2}/6$ triangles in a graph with $e$ edges. Since the pair shadows are disjoint,
$\sum_c(6|A_c|/u^3)^{2/3}\le1$, which implies the displayed inequality. Thus some original center has degree at least $(1-o(1))u^3/6=(1-o(1))\binom n3$. This proves star stability.

#### III.B.6 Eventual exactness and both equality families

Section III.C proves the following finite statement. For a specified vertex $v$, put $w=n-1$ and $q=\binom w3-d_H(v)$. If $w\ge1000$ and $q\le w^3/10000$, then

$$
|H|\le\binom w3+\lfloor w/4\rfloor.
$$

For an extremal sequence, the complete-star lower bound and stability supply such a vertex with $q=o(n^3)$. The local theorem therefore applies for all sufficiently large $n$.

The lower construction is a complete star at $v$, together with a matching of $\lfloor w/4\rfloor$ outside four-sets. A disjoint edge pair whose union contains $v$ has one outside block; two distinct matching blocks cannot both fit in the other seven vertices, so the block and then the star edge are determined. Pairs avoiding $v$ are determined by their matching blocks. The construction is admissible.

The local equality classification gives exactly:

1. A complete star and a maximum outside matching.
2. When $n\equiv0\pmod4$, delete one star edge $vP$. Take outside edges $Px,Qx$, where $P,Q$ are disjoint triples and $x\notin P\cup Q$, and a matching covering the remaining outside vertices.

Both forms are admissible, as verified in §III.C. ∎

### III.C. The finite local theorem

The following finite theorem is logically prior to the asymptotic conclusion. Its coarse estimate is proved in §I.1.

**Theorem III.2 (rank-four local exactness).** Let $H$ be admissible on $W\cup\\{v\\}$, $w=|W|\ge1000$. Let $M$ be the triples missing from the $v$-star, $q=|M|$, and let $B$ be the outside family, $b=|B|$. If $q\le w^3/10000$, then

$$
|H|=\binom w3-q+b\le\binom w3+\lfloor w/4\rfloor. \tag{III.C.1}
$$

If $|H|\ge\binom w3$, then $B$ is linear and $4b\le q+w$. Equality in (III.C.1) has exactly the two forms stated in §III.B.

**Proof.**

#### III.C.1 The two incidence facts

Write $\mu_k(P)=|\\{S\in M:P\subseteq S\\}|$.
If outside edges $E,F$ intersect in $s$ vertices and $k=4-s$, then

$$
\mu_k(E\setminus F)+\mu_k(F\setminus E)
\ge\binom{w-4-k}{3-k},\qquad
q\ge\binom{w-4-k}{3-k}. \tag{III.C.2}
$$

For each $(s-1)$-set $X$ outside $E\cup F$, at least one of
$(E\setminus F)\cup X,(F\setminus E)\cup X$ is missing: otherwise the two star extensions and $E,F$ form a forbidden trade. These pairs of triples are disjoint as $X$ varies, proving both bounds.

For any linear outside subfamily $\mathcal T$ on $U\subseteq W$,

$$
4|\mathcal T|\le |U|+|M\cap\binom U3|. \tag{III.C.3}
$$

Count incidences $(E,a)$ using the opposite facet $E-a$. A missing facet has at most one completion in a linear family. At a fixed $a$, two present opposite facets would be disjoint members of the intersecting common cell $J_{va}(H)$. Thus there is at most one present incidence per vertex.

#### III.C.2 Separate the exceptional vertices and pairs

Put

$$
\Lambda=\binom{w-5}2,\quad
D=\\{a:\mu_1(a)\ge\Lambda/2\\},\quad d=|D|,\quad
U=W\setminus D,\quad u=|U|.
$$

Then

$$
d\le6q/\Lambda. \tag{III.C.4}
$$

Every triple has at most one outside completion in $U$, since two such completions would contradict (III.C.2) with $s=3$. This applies even to triples meeting $D$.

Let $B_i$ be the outside edges with exactly $i$ vertices in $D$, and write $b_i=|B_i|$, $q_U=|M\cap\binom U3|$, $q_D=q-q_U$.
Call a pair $P\subset U$ bad if $\mu_2(P)\ge(w-6)/2$; let their number be $h$. Then

$$
h\le6q/(w-6). \tag{III.C.5}
$$

At any fixed pair root $P$, the pair tails completing it to $B_0$ form a matching, by unique completion of triples in $U$. At most one tail is nonbad, since two would contradict (III.C.2) with $s=2$.

Form a graph on the bad pairs, joining disjoint $P,Q$ when $P\cup Q\in B_0$. This graph is $C_4$-free. A hypothetical four-cycle has disjoint adjacent pairs; if opposite pairs overlap, two outside edges share a triple, impossible. Thus all four physical pairs are mutually disjoint and their union edges give a forbidden trade.

The edges of $B_0$ containing a bad pair number at most $h+e(G)$: an edge split into a bad and a nonbad pair is charged to its unique bad-root/nonbad-tail completion, and every remaining dirty edge is represented by a graph edge. The other edges of $B_0$ form a linear family by (III.C.2).

For a $C_4$-free graph on $h$ vertices, each vertex pair has at most one common neighbor, so $\sum_v\binom{d(v)}2\le\binom h2$. Writing $e=e(G)$, Cauchy gives $4e^2/h-2e\le h(h-1)$, hence

$$
e(G)\le\tfrac12h^{3/2}+\tfrac14h.
$$

Apply (III.C.3) to the clean family and add the dirty edges:

$$
b_0\le(q_U+u)/4+(5/4)h+(1/2)h^{3/2}. \tag{III.C.6}
$$

#### III.C.3 Pay for edges meeting the exceptional set

Set $J=\binom d2(w-2)$ and $\Delta=\binom w2-\Lambda=5w-15$. Missing-degree counting yields

$$
d\Lambda/2\le\sum_{a\in D}\mu_1(a)\le q_D+J.
$$

The last error bounds the excess multiplicity of missing triples containing two or more exceptional vertices.

Each $B_1$-edge has three opposite facets retaining its exceptional vertex; all have distinct completions in $U$. Hence

$$
3b_1\le d\binom u2\le d\Lambda+d\Delta,\qquad
b_1\le(2/3)q_D+(2/3)J+d\Delta/3.
$$

Deleting an ordinary vertex by a fixed rule maps $B_2\cup B_3$ injectively into triples containing at least two exceptional vertices, again by unique completion in $U$. Thus $b_2+b_3\le J$. The finite coarse bound (I.2) gives $b_4\le32d^3$. Combining with (III.C.6),

$$
b\le q_U/4+2q_D/3+u/4+5h/4+h^{3/2}/2
+5J/3+d\Delta/3+32d^3. \tag{III.C.7}
$$

For $w\ge20$, (III.C.4)--(III.C.5) imply $d\le24q/w^2$, $h\le9q/w$. Use these, $J\le d^2w/2$, $\Delta\le5w$, and $b_4\le32d^3$ in (III.C.7):

$$
b\le\frac w4+q\left[
\frac23+\frac{205}{4w}+\frac{27}{2}\sqrt{\frac q{w^3}}
+480\frac q{w^3}+442368\left(\frac q{w^3}\right)^2
\right]. \tag{III.C.8}
$$

For $w\ge1000$ and $q/w^3\le10^{-4}$, the bracket is at most

$$
\frac23+\frac{205}{4000}+\frac{27}{200}
+\frac{480}{10000}+\frac{442368}{10^8}\lt\frac{11}{12}.
$$

#### III.C.4 Exact linearization

Assume $|H|\ge\binom{w}{3}$, so $b\ge q$. Equation (III.C.8) gives $q\le3w$; then $d\le\frac{72}{w}\lt1$, so $D$ is empty. Equation (III.C.5) gives $h\le18$ by integrality. Now (III.C.6) implies

$$
b\le\frac{q+w}{4}+61,\qquad q\le\frac{w+244}{3}\lt w-6.
$$

Any outside intersection of size two would contradict (III.C.2), and intersections of size three are already excluded. Thus $B$ is linear. Equation (III.C.3) gives $4b\le q+w$, proving (III.C.1). If $|H|\lt\binom{w}{3}$, (III.C.1) is immediate.

#### III.C.5 Equality and admissibility of both forms

Write $w=4t+s$, $0\le s\le3$. At equality, $b=q+t$ and $4b\le q+w$, hence $3q\le s$.

If $q=0$, (III.C.2) rules out any intersecting outside pair. Thus $B$ is a matching of size $t$.

Otherwise $q=1,s=3$. Let $P$ be the unique missing triple. Here $4b=w+1$, so equality holds in the incidence proof of (III.C.3). There is exactly one missing-facet incidence, of the form $(Px,x)$, and exactly one present incidence at every vertex. Consequently $x$ has outside degree two and every other vertex degree one. The second edge at $x$ is $Qx$, with $P,Q$ disjoint, and all other outside edges form a matching covering the remaining vertices. The omitted star edge is $vP$.

Conversely, the outside family in either construction is linear and therefore contains no forbidden trade: an edge could intersect the other disjoint pair in at most two vertices, not all four. A forbidden trade involving the star would have two star edges and two outside edges. The outside edges cannot be disjoint, since they must both fit in the other seven vertices. The first construction has no intersecting outside pair. In the second its only intersecting pair is $Px,Qx$; the required star edges are $vP,vQ$, and $vP$ was deleted. Both constructions are admissible. ∎

## IV. Every fixed rank at least five

This part uses the finite coarse estimate of §I.1, then proves an exact local theorem near a star and a coefficient-preserving extraction far from every star. Center cleanup and prefix collision then rule out a positive-mass far-star family. The arguments are finite at each $n$; all asymptotic constants depend only on the fixed rank.


### IV.1 Notation and elementary trade lemmas

An $r$-graph $F\subseteq\binom Vr$ is **admissible** if it has no four distinct edges $A,B,C,D$ such that $A\cap B=C\cap D=\varnothing$ and $A\cup B=C\cup D$. Write $n=|V|$, let $g_r(n)$ be the maximum size of an admissible $r$-graph on $n$ vertices, and put $d_F(S)=|\\{E\in F:S\subseteq E\\}|$, $D_j(F)=\max_{|S|=j}d_F(S)$, and $\partial F=\\{T:|T|=r-1,\ T\subset E\in F\\}$. For disjoint sets, concatenation such as $AP$ denotes $A\cup P$; a vertex in such an expression denotes its singleton. A facet is private if its degree is one. Throughout, $O_r$ constants depend only on $r$; any additional dependence is displayed.

For disjoint nonempty $s$-sets $P,Q$, put

$$
\mathcal C_s(P,Q;F)=\\{A\in\binom{V\setminus(P\cup Q)}{r-s}:A\cup P,A\cup Q\in F\\}.
\tag{IV.1.1}
$$

This family is intersecting: disjoint $A,B$ would give the two different partitions $(A\cup P,B\cup Q)$ and $(A\cup Q,B\cup P)$. In particular the common facet family $J_{xy}(F)=\mathcal C_1(x,y;F)$ is intersecting.

**Lemma IV.1.1 (intersecting covers).** A nonempty intersecting $k$-uniform family is covered by the $k$ vertex stars through any one member. If its total intersection is empty, it is covered by at most $k^2$ pair stars. If its total intersection has at least two points, one pair star covers it.

**Proof.** For the pair-star assertion, fix $A$ in the family. For each $x\in A$, choose a member $B_x$ avoiding $x$. Any member $C$ meets $A$ at some $x$ and meets $B_x$ at some $y\ne x$, so it contains one of the at most $k^2$ pairs $xy$. The other assertions are immediate. Empty families require no cover. ∎

Thus an intersecting $k$-family has $O_k(n^{k-1})$ members. Applied to (IV.1.1), the lemma also gives

$$
|\mathcal C_s(P,Q;F)|\le kD_{s+1}(F),\qquad k=r-s,
\tag{IV.1.2}
$$

and, whenever the total intersection is empty or has at least two points,

$$
|\mathcal C_s(P,Q;F)|\le k^2D_{s+2}(F)\quad(k\ge2).
\tag{IV.1.3}
$$

For example, a cell member containing a fixed pair $xy$ corresponds to an edge through the fixed $(s+2)$-set $Pxy$. This explains the codegree in (IV.1.3).

**Lemma IV.1.2 (distance packing).** Let $\mathcal T\subseteq\binom Wt$ and suppose $|A\setminus B|\ge d$ for different members. If $t<d$, then $|\mathcal T|\le1$. Otherwise

$$
|\mathcal T|\binom t{t-d+1}\le\binom{|W|}{t-d+1}.
\tag{IV.1.4}
$$

**Proof.** Two members cannot share a $(t-d+1)$-subset. Count these subsets inside members. ∎

### IV.2 An exact local theorem for every fixed $r\ge5$

Fix $v$, let $W=V\setminus\\{v\\}$ and $w=|W|$. Let $M$ be the missing $(r-1)$-sets of the $v$-star, $q=|M|$, and let $B=\\{E\in F:v\notin E\\}$, $b=|B|$. Then

$$
|F|=\binom w{r-1}-q+b.
\tag{IV.2.1}
$$

For $P\in\binom Wk$ set $\mu_k(P)=|\\{S\in M:P\subseteq S\\}|$ and

$$
\Lambda_k=\binom{w-r-k}{r-k-1}\qquad(1\le k\le r-1).
$$

We take $w$ sufficiently large in terms of the fixed rank.

If outside edges $E,E'$ intersect and $|E\setminus E'|=k$, then

$$
\mu_k(E\setminus E')+\mu_k(E'\setminus E)\ge\Lambda_k,
\qquad q\ge\Lambda_k.
\tag{IV.2.2}
$$

Indeed, for each $(r-k-1)$-set $X$ outside $E\cup E'$, at least one of $(E\setminus E')\cup X$ and $(E'\setminus E)\cup X$ is missing. Otherwise the two star edges and $E,E'$ give a forbidden trade. The two candidate missing sets, over all $X$, are distinct, including between the two sides, since $X$ avoids $E\cup E'$.

Call a $k$-set bad if $\mu_k(P)\ge\Lambda_k/2$, and write $\mathcal H_k$ for the bad sets. Incidence counting gives

$$
|\mathcal H_k|\le\frac{2\binom{r-1}k q}{\Lambda_k}
=O_r\\!\left(\frac q{w^{r-k-1}}\right),\qquad k\le r-2.
\tag{IV.2.3}
$$

Let $D=\mathcal H_1$, $d=|D|$, and $U=W\setminus D$, $u=|U|$. Then

$$
d=O_r(q/w^{r-2}).
\tag{IV.2.4}
$$

Every $(r-1)$-set, even one meeting $D$, has at most one completion in $U$ to an outside edge: two such completions would violate (IV.2.2) for $k=1$.

#### IV.2.1 Cleaning outside edges on $U$

We show that all but

$$
O_r\\!\left(\frac q w+\frac{q^2}{w^{r-1}}\right)
\tag{IV.2.5}
$$

edges of $B[U]$ belong to a linear family. The following distance estimate supplies the needed deletion bound.

Put $h=|\mathcal H_2\cap\binom U2|=O_r(q/w^{r-3})$.

First count edges containing exactly one bad pair. For a fixed bad pair $P$, their tails $E\setminus P$ have size $r-2$ and contain no bad pairs. Two distinct tails cannot have distance one, by the unique completion property on $U$, or distance two, by (IV.2.2), because both difference pairs are nonbad. Their distance is therefore at least three. Lemma IV.1.2 bounds their number by $O_r(w^{r-4})$. Summing over $P$ gives $O_r(q/w)$.

Next count edges containing two disjoint bad pairs. For fixed such pairs their union has size four. The remaining $(r-4)$-tails have distance at least two, again by unique facet completion. Lemma IV.1.2 gives $O_r(w^{r-5})$ tails, including the bound one when $r=5$. The total is $O_r(h^2w^{r-5})=O_r(q^2/w^{r-1})$.

For edges with at least two bad pairs but no two disjoint bad pairs, fix two bad pairs whose union $S$ has size three. No remaining tail $E\setminus S$ contains a bad pair, as that pair would be disjoint from either of the fixed pairs. Two tails cannot have distance one or two, by the same two arguments as above. Their size is $r-3$, so Lemma IV.1.2 bounds their number by $O_r(w^{r-5})$, with at most one when $r=5$. Summing over at most $h^2$ choices gives the same quadratic error. Multiple counting only enlarges these upper bounds. This exhausts edges containing a bad pair.

For each remaining edge with a bad set of size at least three, let $k\in\\{3,\ldots,r-2\\}$ be its smallest bad-set size. Fix a bad $k$-set $P$. The tails of edges in this class through $P$ have size $r-k$ and mutual distance at least $k$: a smaller positive difference would have two nonbad sides and contradict (IV.2.2). Lemma IV.1.2 gives

$$
O_r\bigl(w^{\max\\{r-2k+1,0\\}}\bigr)
$$

tails. Multiplying by (IV.2.3) is $O_r(q/w)$: if $r-2k+1\ge0$, the exponent ratio is $w^{2-k}\le w^{-1}$; otherwise $r-k-1\ge1$. There are only finitely many $k$.

After these deletions no edge contains a bad set of any size $1,\ldots,r-2$. Two surviving edges intersecting in at least two vertices would have a difference of size at most $r-2$, contradicting (IV.2.2). Thus the survivor is linear, proving (IV.2.5).

For any linear $\mathcal T\subseteq B[U]$,

$$
r|\mathcal T|\le u+|M\cap\binom U{r-1}|.
\tag{IV.2.6}
$$

Count incidences $(E,a)$ by opposite facets $E\setminus\\{a\\}$. A missing facet has at most one completion in a linear family. At a fixed $a$, two present opposite facets would be disjoint members of $J_{va}(F)$, impossible. Hence at most one present incidence is charged to each vertex. Writing $q_U=|M\cap\binom U{r-1}|$ gives

$$
|B[U]|\le(q_U+u)/r+O_r(q/w+q^2/w^{r-1}).
\tag{IV.2.7}
$$

#### IV.2.2 Exceptional vertices and contraction

Let $b_i$ count outside edges with $i$ vertices in $D$ and put $q_D=q-q_U$, $\Lambda=\Lambda_1$,

$$
J=\binom d2\binom{w-2}{r-3},\qquad
\Delta=\binom w{r-2}-\Lambda=O_r(w^{r-3}).
$$

Missing-set multiplicity and the definition of $D$ give

$$
d\Lambda/2\le\sum_{a\in D}\mu_1(a)\le q_D+J.
\tag{IV.2.8}
$$

The upper error follows from $i-1\le\binom i2$ for a missing set meeting $D$ in $i$ points. Every $b_1$ edge supplies $r-1$ distinct opposite facets retaining its exceptional vertex, and each has at most one completion in $U$. Therefore

$$
b_1\le\frac{d\binom u{r-2}}{r-1}
\le\frac{2q_D+2J+d\Delta}{r-1}.
\tag{IV.2.9}
$$

An edge meeting $D$ at least twice and $U$ at least once maps injectively to a facet with at least two exceptional points by deleting a vertex of $U$ according to a fixed rule. The injection uses the same unique completion property. Thus $\sum_{i=2}^{r-1}b_i\le J$. Theorem I.1 gives $b_r=O_r(d^{r-1})=O_r(d^2w^{r-3})$. By (IV.2.4),

$$
J+b_r=O_r(q^2/w^{r-1}),\qquad d\Delta=O_r(q/w).
$$

Together with (IV.2.7) and (IV.2.9), we obtain the sufficient contraction

$$
\boxed{
b\le\frac{2}{r-1}q+\frac wr
+C_r\left(\frac q w+\frac{q^2}{w^{r-1}}\right).
}\tag{IV.2.10}
$$

The coefficient in (IV.2.10) is strictly below one for every $r\ge5$, which is exactly what the local argument requires.

#### IV.2.3 Exactness and equality

**Theorem IV.2.1.** For each fixed $r\ge5$, there exist $\delta_r>0$ and $w_0(r)$ such that $w\ge w_0(r)$ and $q\le\delta_rw^{r-1}$ imply

$$
|F|\le\binom w{r-1}+\lfloor w/r\rfloor.
\tag{IV.2.11}
$$

If $|F|\ge\binom w{r-1}$, the outside family is linear and $rb\le w+q$.

**Proof.** The conclusion is immediate if $b<q$. Otherwise put $a_r=2/(r-1)<1$ and choose $\delta_r$ small and $w_0$ large enough that $C_r(\delta_r+1/w)\le(1-a_r)/2$. Equation (IV.2.10) then implies

$$
q\le b\le\frac{1+a_r}{2}q+w/r,
\qquad q\le\beta_rw,\quad
\beta_r=\frac{2(r-1)}{r(r-3)}<1.
$$

Increase $w_0$ so that $\beta_rw<w-2r+2$. For $1\le k\le r-2$, put $j=r-k-1\ge1$ and $A=w-2r+2$; then $\Lambda_k=\binom{A+j-1}j\ge A$. Thus (IV.2.2) excludes every outside intersection of size at least two. The whole outside family is linear, and (IV.2.6) with $U=W$ yields $rb\le w+q$. Consequently $b-q\le w/r-(r-1)q/r\le w/r$; integrality proves (IV.2.11). ∎

At equality write $w=rt+s$, $0\le s<r$. Then $b=q+t$ and $rb\le w+q$ give $(r-1)q\le s$. Hence either $q=0$, or $q=1$ and $s=r-1$. If $q=0$, (IV.2.2) also excludes one-point intersections, so $B$ is a maximum matching. If $q=1$, let $P$ be the unique missing facet. The incidence proof has equality, with exactly one missing-facet incidence and exactly one present incidence at every vertex. Hence there is an edge $Px$, $x$ has outside degree two, and all other vertices have degree one. The other edge at $x$ is $Qx$, where $P,Q$ are disjoint $(r-1)$-sets, and all remaining edges form a matching on the remaining vertices. Conversely these two constructions are admissible: a linear family of rank at least three contains no forbidden trade, and in a trade involving $v$ the only possible intersecting outside pair is $Px,Qx$, which would require the deleted star edge $vP$.

### IV.3 Shadow allocation for star layers

We give the elementary shadow estimate needed to control many centers at once. It will be used both in the initial far-star reduction and inside each regularization round.

**Lemma IV.3.1 (shadow power inequality).** If $\mathcal A\subseteq\binom Uk$, $k\ge2$, and $\partial\mathcal A$ is its $(k-1)$-shadow, then

$$
(k!|\mathcal A|)^{k-1}\le((k-1)!|\partial\mathcal A|)^k.
\tag{IV.3.1}
$$

**Proof.** For a finite probability law $p$, set $H(p)=-\sum_xp(x)\log p(x)$, with $0\log0=0$; write $H(X)$ for the entropy of the law of $X$. The inequality $\log t\le t-1$ follows by differentiating $t-1-\log t$. For probability laws $p,q$ with $q>0$ on the support of $p$, it gives
$D(p\Vert q):=\sum_xp(x)\log(p(x)/q(x))\ge0$.
If $p=\sum_j\lambda_jp_j$, then
$H(p)-\sum_j\lambda_jH(p_j)=\sum_j\lambda_jD(p_j\Vert p)\ge0$.
Thus entropy is concave. Applying $D(p\Vert q)\ge0$ with $q$ uniform on the support gives $H(p)\le\log|\operatorname{supp}p|$. The chain rule $H(X,Y)=H(X)+H(Y\mid X)$ follows by expanding the sums. Concavity applied to conditional laws shows that further conditioning cannot increase conditional entropy.

For a random vector $(X_1,\ldots,X_k)$, expand each $H(X_{-i})$ in coordinate order. Each term $H(X_j\mid\text{preceding coordinates except }i)$ is at least $H(X_j\mid X_1,\ldots,X_{j-1})$. Every $j$ occurs in $k-1$ of these expansions, proving

$$
\sum_iH(X_{-i})\ge(k-1)H(X_1,\ldots,X_k).
$$

Take the uniform ordered $k$-tuple whose underlying set lies in $\mathcal A$. Its entropy is $\log(k!|\mathcal A|)$; each deletion projection has support at most $(k-1)!|\partial\mathcal A|$. Exponentiating proves (IV.3.1). The empty family is immediate. ∎

Consequently, if the $(k-1)$-shadows of families $\mathcal A_i\subseteq\binom Uk$ are disjoint, $u=|U|$, and $M=\max_i|\mathcal A_i|$, then

$$
\sum_i|\mathcal A_i|
\le M^{1/k}\sum_i|\mathcal A_i|^{(k-1)/k}
\le \frac{u^{k-1}}{(k!)^{(k-1)/k}}M^{1/k}.
\tag{IV.3.2}
$$

The second inequality uses (IV.3.1), disjointness, and $(k-1)!\binom u{k-1}\le u^{k-1}$. Families of size zero may be omitted.

**Lemma IV.3.2 (separating star shadows).** Let $z_1,\ldots,z_h$ lie outside $U$ and let $F$ be admissible. Set $k=r-1$ and $\mathcal A_i=\\{T\in\binom Uk:z_iT\in F\\}$. Deleting at most $O_r(hn^{k-1/2})$ colored members makes their $(k-1)$-shadows disjoint, where $|U|\le n$. If, in addition, $D_j(F)\le Rn^{r-j-1}$ for $j=2,3$, the deletion cost is at most $O_r(h\sqrt R\\,n^{r-2})$.

**Proof.** For $P\in\binom U{k-1}$ let $d_i(P)=|\\{x:Px\in\mathcal A_i\\}|$. For $i\ne j$, equal completions in $\sum_Pd_i(P)d_j(P)$ contribute $k|\mathcal A_i\cap\mathcal A_j|$. This intersection is intersecting, so this term is $O_r(n^{k-1})$, or $O_r(D_2(F))$ by (IV.1.2).

For distinct completions $x,y\in U$, the possible $P$ form the intersecting common-core family of the disjoint roots $\\{z_i,x\\}$ and $\\{z_j,y\\}$. There are $O_r(n^{k-2})$ such $P$, or at most $(k-1)D_3(F)$ by (IV.1.2). Sum over $x,y$ to obtain

$$
\sum_Pd_i(P)d_j(P)=O_r(n^k),
\quad\text{or respectively }O_r(Rn^{r-2}).
\tag{IV.3.3}
$$

Assign each $P$ to an index maximizing $d_i(P)$ and delete every colored member containing a $P$ assigned elsewhere. If $s_P$ is the sum of nonmaximal entries, then $s_P^2\le2\sum_{i<j}d_i(P)d_j(P)$: each nonmaximal square is at most the maximal entry times that entry. The number deleted is at most $\sum_Ps_P$. Cauchy–Schwarz over at most $n^{k-1}$ sets $P$ and (IV.3.3) give the two bounds. Every surviving shadow set has a single owner. ∎

**Corollary IV.3.3 (far-star tail).** Fix $r\ge4$ and $0<\delta<1$. Suppose $|F|\ge M_n:=\binom{n-1}{r-1}$ and $\max_vd_F(v)\le(1-\delta)M_n$. If $X\subseteq V$ has $h=o(\sqrt n)$ vertices, then

$$
|F[V\setminus X]|\ge
\bigl(1-(1-\delta)^{1/(r-1)}-o_r(1)\bigr)M_n.
\tag{IV.3.4}
$$

The error is uniform in $F,X$ with the specified $h$.

**Proof.** Edges meeting $X$ at least twice number at most $\binom h2\binom{n-2}{r-2}=o(n^{r-1})$. For the exactly-once layer, apply Lemma IV.3.2 and then (IV.3.2) with $k=r-1$, $u\le n$ and maximal star-link size at most $(1-\delta)M_n$. The deleted colored members number $o(n^k)$, and the remaining total is at most $((1-\delta)^{1/k}+o(1))M_n$. Subtract the two layers from $|F|\ge M_n$. ∎

### IV.4 Uniform regularization at natural codegree scales

**Theorem IV.4.1 (one contraction round).** For fixed $r\ge4$, let

$$
\eta_r=\min\\{1/8,1/(2(r-1))\\}.
$$

There are constants $R_{\ast}(r),C_r$ such that if $R_{\ast}\le R\le n^{2/3}$ and an admissible family $H$ satisfies

$$
D_j(H)\le Rn^{r-j-1}\qquad(1\le j\le r-1),
\tag{IV.4.1}
$$

then some $H'\subseteq H$ satisfies

$$
|H\setminus H'|\le C_rR^{-\eta_r}n^{r-1},\qquad
D_j(H')\le R^{3/4}n^{r-j-1}\quad(1\le j\le r-1).
\tag{IV.4.2}
$$

The constants do not depend on $R$ or on the particular family.

**Proof.** Put $T=R^{5/8}$. For each $s\in\\{1,\ldots,r-2\\}$, call an $s$-set heavy if its degree exceeds $Tn^{r-s-1}$. We first cover all such sets by $O_r(n/T)$ vertices.

For a matching of $a$ heavy $s$-sets, put $q=r-s\ge2$ and select $d=\lfloor Tn^{q-1}\rfloor+1$ tails at each root. Each pair of selected tail families has intersection at most $qRn^{q-2}$ by (IV.1.2). Multiplicities on at most $n^q$ tails and Cauchy–Schwarz give

$$
(ad)^2\le n^q\bigl(ad+a^2qRn^{q-2}\bigr).
$$

Since $T^2/R=R^{1/4}$, choosing $R_{\ast}$ large makes the quadratic error at most half the left quadratic coefficient. Thus $a\le2n^q/d\le2n/T$. A maximal matching covers the heavy sets by at most $2sn/T$ vertices. The union $X$ over the finitely many $s$ has $h=|X|=O_r(n/T)$.

Edges meeting $X$ at least twice number at most

$$
\binom h2D_2(H)=O_r((R/T^2)n^{r-1}).
\tag{IV.4.3}
$$

For edges meeting $X$ exactly once, Lemma IV.3.2 deletes $O_r(h\sqrt R\\,n^{r-2})=O_r((\sqrt R/T)n^{r-1})$ colored members to separate their shadows. The surviving link sizes are each at most $D_1(H)\le Rn^{r-2}$. Equation (IV.3.2) bounds their total by

$$
O_r\bigl(n^{r-2}(Rn^{r-2})^{1/(r-1)}\bigr)
=O_r\bigl((R/n)^{1/(r-1)}n^{r-1}\bigr).
\tag{IV.4.4}
$$

Consequently the entire layer touching $X$ can be deleted at cost

$$
O_r\left[R^{-1/4}+R^{-1/8}+(R/n)^{1/(r-1)}\right]n^{r-1}
=O_r(R^{-\eta_r}n^{r-1}),
\tag{IV.4.5}
$$

where the last step uses $R\le n^{2/3}$, hence $R/n\le R^{-1/2}$.

Let $H_0=H[V\setminus X]$. All degrees of orders $1,\ldots,r-2$ are now at most $Tn^{r-j-1}$. The exact facet-energy identity is

$$
\sum_{A\in\binom V{r-1}}\binom{d_{H_0}(A)}2
=\sum_{x<y}|J_{xy}(H_0)|.
\tag{IV.4.6}
$$

Each common cell is intersecting, so (IV.1.2) bounds it by $(r-1)D_2(H_0)\le(r-1)Tn^{r-3}$. The energy is therefore $O_r(Tn^{r-1})$. Delete edges containing a facet of degree greater than $R^{3/4}$. Their number is at most

$$
\sum_{A:d(A)>R^{3/4}}d(A)
\le\frac{2}{R^{3/4}-1}\sum_A\binom{d(A)}2
=O_r(R^{-1/8}n^{r-1}).
\tag{IV.4.7}
$$

The final facet degrees have the required bound, and the lower degrees remain at most $Tn^{r-j-1}\le R^{3/4}n^{r-j-1}$. This proves (IV.4.2). ∎

The proof controls actual deleted edges. Its shadow-allocation argument is a finite counting step, so it applies uniformly for the varying $R$ used in the iteration.

**Corollary IV.4.2 (iteration).** If the starting natural factor is $R_0\le n^{2/3}$, and $L=L(n)\to\infty$ with $L<R_0$, one can reach factor at most $L$ while losing

$$
O_r\\!\left(\frac{L^{-\eta_r}}{1-L^{-\eta_r/3}}\right)n^{r-1}=o(n^{r-1})
\tag{IV.4.8}
$$

edges.

**Proof.** Apply Theorem IV.4.1 with successive factors $R_i=R_0^{(3/4)^i}$, stopping at the first factor at most $L$. Read the preceding factors backwards from the last applied one, which exceeds $L$. They are larger than $L^{(4/3)^j}$, $j\ge0$. Since $(4/3)^j\ge1+j/3$, their losses sum to the displayed geometric bound. All applied factors eventually exceed $R_{\ast}$ and remain at most $n^{2/3}$. If $R_0\le L$, no iteration is needed. ∎

### IV.5 Coefficient-preserving extraction

We first produce a positive-mass family in the range of Theorem IV.4.1.

**Lemma IV.5.1 (initial square-root factor).** Under the hypotheses of Corollary IV.3.3, let $X_0$ be the $h_0=\lfloor\sqrt n/\log n\rfloor$ vertices of largest degree. There is $G\subseteq F[V\setminus X_0]$ such that

$$
|F[V\setminus X_0]\setminus G|=o(n^{r-1}),\quad |G|\ge c_{r,\delta}n^{r-1},
\quad D_j(G)\le C_r\sqrt n\log^3n\\,n^{r-j-1}.
\tag{IV.5.1}
$$

**Proof.** Corollary IV.3.3 supplies the positive mass before the further deletion. Theorem I.1 and the degree sum $\sum_vd_F(v)=r|F|$ give

$$
D_1(F[V\setminus X_0])\le r|F|/(h_0+1)
=O_r(n^{r-3/2}\log n).
$$

Put $\tau=\log^3n/\sqrt n$. For each $2\le s\le r-1$, call an $s$-set heavy at degree $\tau\binom n{r-s}$. Links at disjoint roots have intersection $O_r(n^{r-s-1})$ by Lemma IV.1.1, also when $r-s=1$. The pointwise inequality $\mathbf1_{\cup_i A_i}\ge\sum_i\mathbf1_{A_i}-\sum_{i<j}\mathbf1_{A_i\cap A_j}$ follows by checking the number of sets containing each point. If a matching of $a=\lceil3/\tau\rceil$ heavy roots existed, summing this inequality over the universe $\binom V{r-s}$ would give

$$
1\ge a\tau-O_r(a^2/n)=3-o(1),
$$

a contradiction, since $n\tau^2=\log^6n\to\infty$. The vertices of maximal heavy matchings over all $s$ form a set $Y$ of size $O_r(\sqrt n/\log^3n)$. Delete every edge touching $Y$. The cost is $O_r(n^{r-1}/\log^2n)$ by the preceding vertex-degree bound. All higher codegrees in the survivor are below their thresholds; vertex degrees only decrease. This proves (IV.5.1), reducing the positive constant if necessary. ∎

For example, $R_0=C_r\sqrt n\log^3n\le n^{2/3}$ for large $n$. Corollary IV.4.2 with $L(n)=\log\log n$ therefore gives $H\subseteq G$ with actual deletion cost $o(n^{r-1})$ and

$$
D_j(H)\le R(n)n^{r-j-1},\qquad R(n)=\log\log n.
\tag{IV.5.2}
$$

It remains to retain the coefficient-one information from $F$, rather than just its positive mass.

**Lemma IV.5.2 (finite shadow ledger).** Let $X\subseteq V$, $h=|X|$, $W=V\setminus X$, $w=|W|$, and $K\subseteq F[W]$. Put $R_{\rm disc}=F[W]\setminus K$. Then

$$
|F|\le\binom w{r-1}+|K|-|\partial K|+|R_{\rm disc}|+\mathcal E(X,K),
\tag{IV.5.3}
$$

where

$$
\mathcal E(X,K)=(r-1)hwD_2(K)
+(r-1)\binom h2\binom{w-1}{r-2}
+\binom h2\binom{n-2}{r-2}.
\tag{IV.5.4}
$$

**Proof.** For $x\in X$ let $L_x=\\{T\in\binom W{r-1}:xT\in F\\}$. First

$$
|L_x\cap\partial K|\le(r-1)wD_2(K).
\tag{IV.5.5}
$$

For each $y\in W$, the family $\\{T\in L_x:yT\in K\\}$ is intersecting, as a subfamily of $J_{xy}(F)$. Cover it by the $(r-1)$ stars through one of its members. Each star gives edges of $K$ through a fixed pair $yz$, so has at most $D_2(K)$ members. Summing over $y$ counts every member of $L_x\cap\partial K$ at least once and proves (IV.5.5).

Also $L_x\cap L_{x'}$ is intersecting, so its size is at most $(r-1)\binom{w-1}{r-2}$. The elementary multiplicity inequality $a\le1+\binom a2$ for positive integers $a$ yields

$$
\sum_{x\in X}|L_x|
\le\left|\bigcup_xL_x\right|+\sum_{x<x'}|L_x\cap L_{x'}|.
$$

The union occupies at most $\binom w{r-1}-|\partial K|+\sum_x|L_x\cap\partial K|$ facets. Finally edges meeting $X$ at least twice number at most $\binom h2\binom{n-2}{r-2}$, while edges avoiding $X$ number $|K|+|R_{\rm disc}|$. Combining these bounds proves (IV.5.3). ∎

**Theorem IV.5.3 (far-star extraction with the shadow surplus retained).** Fix $r\ge4$ and $\delta>0$. For every admissible sequence $F$ with $|F|\ge M_n$ and $\max_vd_F(v)\le(1-\delta)M_n$, there are $H\subseteq F$ and fixed constants $c,C>0$ such that

$$
cn^{r-1}\le|H|\le Cn^{r-1},\qquad
D_j(H)\le Rn^{r-j-1}\ (1\le j\le r-1),
\tag{IV.5.6}
$$

$$
\boxed{|H|-|\partial H|\ge |F|-M_n-o(n^{r-1}),\qquad R=\log\log n.}
\tag{IV.5.7}
$$

The error bounds are uniform over the families for fixed $r,\delta$. In particular, the assertion applies when the normalized excess over $M_n$ tends to zero.

**Proof.** Use Lemma IV.5.1 and Corollary IV.4.2. They preserve a fixed positive fraction of the tail mass and delete $o(n^{r-1})$ edges from $F[V\setminus X_0]$. Apply Lemma IV.5.2 with this same initial $X_0$ and $K=H$. Its first error is

$$
O_r\bigl(h_0n\\,Rn^{r-3}\bigr)
=O_r(Rn^{r-3/2}/\log n)=o(n^{r-1}),
$$

and its other two errors are $O_r(h_0^2n^{r-2})=O_r(n^{r-1}/\log^2n)$. The discarded-family term is also $o(n^{r-1})$. Since $|V\setminus X_0|\le n-1$, the binomial term is at most $M_n$. Rearrangement proves (IV.5.7). Theorem I.1 supplies the upper constant in (IV.5.6). ∎

### IV.6 Finite color rigidity and its quantitative form

A fully colored triangle is **bicolored** if its three edges use exactly two colors.

**Lemma IV.6.1.** A complete graph with at most $q\ge2$ edge colors and no bicolored triangle is either monochromatic or has at most $(q-1)^2$ vertices.

**Proof.** Suppose a monochromatic clique $C$ has at least $q$ vertices, with color $c$. For a vertex $x$ outside $C$, its edges into $C$ cannot mix $c$ with another color. If none has color $c$, they must have pairwise different colors, or a bicolored triangle results. There are only $q-1$ alternative colors, fewer than $|C|$. Thus every edge from $x$ into $C$ has color $c$. A triangle through $C$ then shows that every edge between outside vertices also has color $c$.

In a graph that is not monochromatic, therefore, every monochromatic clique has at most $q-1$ vertices. At any vertex $x$, its neighbors joined by a given color together with $x$ form a monochromatic clique, so each color accounts for at most $q-2$ neighbors. Consequently the order is at most $1+q(q-2)=(q-1)^2$. ∎

**Lemma IV.6.2 (quantitative coloring lemma).** Partially color the edges of a complete graph on $m$ vertices using at most $q\ge2$ colors. Let $b$ be the number of uncolored edges and $\beta$ the number of fully colored bicolored triangles. Set

$$
h=\max\\{4,(q-1)^2+1\\}.
$$

If $m\ge h$, some color occupies all but at most

$$
\binom h2 b+\frac{3\binom h3}{m-2}\\,\beta
\tag{IV.6.1}
$$

edges. Uncolored edges are included in this exception count.

**Proof.** A uniformly chosen $h$-set is bad if it contains an uncolored pair or a bicolored triangle. The probability of this event is at most

$$
\delta=\frac{\binom h2}{\binom m2}b+
\frac{\binom h3}{\binom m3}\beta.
$$

Every other $h$-set is monochromatic by Lemma IV.6.1. Take two independent uniformly chosen edges of the complete graph, permitting equality. Conditional on their union having size $t\in\\{2,3,4\\}$, their distribution can equivalently be generated by first choosing a uniform $h$-set and then a uniform ordered pair of its edges with union size $t$. Indeed every global ordered pair of that type lies in exactly $\binom{m-t}{h-t}$ such $h$-sets. Thus, for each type, the probability that the two edges are not both colored with the same color is at most $\delta$.

Let $p_i$ be the fraction of all edges having color $i$. Independence gives $\sum_i p_i^2\ge1-\delta$. Since $\sum_i p_i\le1$, $\max_i p_i\ge\sum_i p_i^2$. At most $\delta\binom m2$ edges fail to have a most frequent color. Expanding this expression gives (IV.6.1). If $\delta\ge1$ the claimed upper bound is trivial. ∎

### IV.7 Common-cell counts and multilevel cleanup

All cells, degrees, thresholds and labels in this section refer to one fixed admissible **parent** $H$. They are never recomputed after edge deletions. Put $D_j=D_j(H)$.

For disjoint $s$-sets $P,Q$, with $k=r-s\ge3$, call the pair strong if $|\mathcal C_s(P,Q;H)|\ge t_s>0$ and the intersection of all its members is a singleton. Write $c_s(P,Q)$ for that singleton's vertex. Thus every member of the cell contains this label, which is uniquely determined by the roots.

#### IV.7.1 Repeated-center degree

For fixed $P,z$, let $\mathcal N_z(P)$ be the strong partners $Q$ labeled $z$. Count pairs $(Q,A)$ with $A\in\mathcal C_s(P,Q;H)$. Each $Q$ contributes at least $t_s$. Each $A$ contains $z$ and gives an edge $AP$ through $Pz$, so there are at most $D_{s+1}$ choices of $A$. For a fixed $A$ there are at most $D_k$ choices of $Q$. Therefore

$$
|\mathcal N_z(P)|\le D_{s+1}D_k/t_s.
\tag{IV.7.1}
$$

More generally, if each $Q$ must contain a prescribed $p$-set $U$ disjoint from $Pz$, every such $A$ avoids $U$ and the second bound improves to $D_{k+p}$. Hence

$$
|\\{Q\in\mathcal N_z(P):U\subseteq Q\\}|
\le D_{s+1}D_{k+p}/t_s.
\tag{IV.7.2}
$$

In particular, prescribing one vertex gains a factor $n$ under the natural codegree bounds. These estimates are direct incidence counts.

#### IV.7.2 Uncolored pairs and bicolored triangles

For a $k$-set $A$ let $m_A=d_H(A)$. On its link

$$
\operatorname{lk}_H(A)=\\{P\in\binom{V\setminus A}s:AP\in H\\}
$$

form a complete graph, coloring $PQ$ by $c_s(P,Q)$ when the pair is disjoint and strong, and otherwise leaving it uncolored. Every color belongs to $A$, so at most $k$ colors occur.

Let $b_A$ and $\beta_A$ be its uncolored-edge and bicolored-triangle counts. With $N_s=\binom ns$, we have

$$
\sum_A b_A\le
B_s(t_s):=\binom{N_s}{2}(k^2D_{s+2}+t_s)
+\frac{s}{2}\binom rk|H|D_{k+1},
\tag{IV.7.3}
$$

$$
\sum_A\beta_A\le
T_s(t_s):=\binom{N_s}{2}\\,
\frac{D_kD_{s+1}D_{s+2}}{t_s}.
\tag{IV.7.4}
$$

For (IV.7.3), a disjoint pair is uncolored only when its cell is too small or has nonsingleton total intersection; Lemma IV.1.1 bounds its number of supporting cores by $t_s+k^2D_{s+2}$. For intersecting link roots, choose an incidence $A\subset E\in H$, then $x\in E\setminus A$, then a distinct edge $AQ\in H$ with $x\in Q$. There are at most $\binom rk|H|\cdot sD_{k+1}$ ordered choices. Every uncolored intersecting pair is counted at least twice, giving the last term.

For (IV.7.4), a bicolored triangle has a unique vertex incident to the two edges of its repeated color. Call this root $P$; write its other two roots as $Q,R$, repeated label $z=c_s(P,Q)=c_s(P,R)$, and different label $w=c_s(Q,R)$. Choose the ordered pair $(P,Q)$ in at most $N_s(N_s-1)$ ways. Its label $z$ is fixed. Equation (IV.7.1) leaves at most $D_kD_{s+1}/t_s$ possibilities for $R$. The label $w$ is then fixed. Every supporting core $A$ contains the distinct vertices $z,w$ and yields an edge $AP$ through $Pzw$, so there are at most $D_{s+2}$ such cores. Every triangle is counted twice, by exchanging $Q,R$. This proves (IV.7.4).

#### IV.7.3 A finite multilevel cleanup bound

**Lemma IV.7.1.** Fix $2\le s\le r-3$, $k=r-s$, and parameters $0<\theta<1$ and $u\ge\max\\{4,(k-1)^2+1\\}$. One can delete at most

$$
\binom nk u+
\frac{C_k}{\theta u}
\left(B_s(t_s)+\frac{T_s(t_s)}{u-2}\right)
\tag{IV.7.5}
$$

edges so that every occurring $k$-core $A$ has a designated center $z_A\in A$, has parent degree $m_A\ge u$, and satisfies the following property: for each retained edge $AP$, at least

$$
m_A-1-\theta m_A
\tag{IV.7.6}
$$

members $Q$ of its **parent** link are disjoint strong partners of $P$ with label $z_A$.

**Proof.** Delete edges through any $A$ of parent degree below $u$; their total is at most $\binom nk u$. For each remaining core, Lemma IV.6.2 supplies a most frequent color $z_A$ with

$$
M_A\le C_k\left(b_A+\frac{\beta_A}{m_A-2}\right)
$$

exceptions among all pairs. If no color occurs, choose any $z_A\in A$; the same exception bound holds. Delete every edge $AP$ whose link vertex $P$ has more than $\theta m_A$ incident exceptions. The number of such link vertices is at most $2M_A/(\theta m_A)$. Summing over cores and using (IV.7.3)–(IV.7.4) gives (IV.7.5), enlarging $C_k$. A retained link vertex has at most $\theta m_A$ exceptions among its $m_A-1$ other vertices, giving (IV.7.6). All centers and exceptional-pair tests were made in $H$; subsequent deletions cannot invalidate this statement about an individual retained edge. ∎

### IV.8 Facet cleanup without deleting private facets

For $s=1$, put $k=r-1$ and use threshold $t_1$. The following deletion procedure makes every shared facet's completion pairs strong with a common parent label.

First delete the two edges corresponding to every occurrence of an uncolored completion pair at a facet. Distinct singleton roots are automatically disjoint, so the cost is at most

$$
2\binom n2\bigl((r-1)^2D_3+t_1\bigr).
\tag{IV.8.1}
$$

Next delete the three edges corresponding to every occurrence of a fully colored bicolored completion triangle. By (IV.7.4) the cost is at most

$$
3\binom n2\\,D_{r-1}D_2D_3/t_1.
\tag{IV.8.2}
$$

Finally delete the three edges of every rainbow completion triangle. For a fixed completion triple $x,y,z$, its three labels are already fixed in the parent. For a rainbow triangle they are distinct; any supporting facet contains all three and avoids $x,y,z$. Thus its edge with completion $x$ contains a fixed four-set, giving at most $D_4$ possibilities. This last cost is at most

$$
3\binom n3 D_4.
\tag{IV.8.3}
$$

After these deletions, every completion graph of size at least two is fully colored and all its triangles are monochromatic. Such a complete graph is monochromatic: two adjacent edges have the same color by their triangle, and disjoint edges can be linked through adjacent ones. The size-two case has just one color already.

Consequently every shared facet $T$ has a center $z_T\in T$ such that every pair of its surviving completions has parent label $z_T$. Facets with a single completion are left in place; no center is required for them. The total deletion bound is the sum of (IV.8.1)–(IV.8.3). The $D_4$ term is precisely why the ensuing application assumes $r\ge5$.

#### IV.8.1 Simultaneous cleanup at the required scale

**Theorem IV.8.1.** Fix $r\ge5$ and $C>0$. Suppose

$$
|H|\le Cn^{r-1},\qquad D_j(H)\le Rn^{r-j-1}\quad(1\le j\le r-1),
$$

where $R\ge1$ and $R^3/n\to0$. Put

$$
\rho=(R^3/n)^{1/8},\qquad
t_s=\rho^3n^{r-s-2}\quad(1\le s\le r-3).
\tag{IV.8.4}
$$

There is $K_0\subseteq H$ with

$$
|H\setminus K_0|=O_{r,C}(\rho n^{r-1})
\tag{IV.8.5}
$$

such that:

1. Every occurring $3\le |A|\le r-2$ core has $z_A\in A$ and parent degree $m_A\ge\rho n^{r-|A|-1}$.

   For each retained edge $AP$, at least $(1-2\rho)m_A$ parent-link members are disjoint strong partners of $P$ with parent label $z_A$.
2. Every facet with at least two $K_0$-completions has a center $z_T\in T$, and all distinct retained completion pairs have the parent label $z_T$.
3. No private-facet stripping is performed.

**Proof.** Apply Lemma IV.7.1 for each $2\le s\le r-3$ with

$$
u_s=\rho n^{s-1},\qquad \theta=\rho.
$$

Since $\rho\ge n^{-1/8}$, both $u_s$ and $\rho u_s$ tend to infinity. In particular $u_s$ exceeds the fixed threshold in Lemma IV.7.1, and the $1$ in (IV.7.6) is at most $\rho m_A$ for large $n$.

Under the stated codegree bounds, (IV.7.3)–(IV.7.4) give

$$
B_s=O_{r,C}\bigl(Rn^{r+s-3}+\rho^3n^{r+s-2}\bigr),\qquad
T_s=O_r\bigl(R^3\rho^{-3}n^{r+2s-4}\bigr).
\tag{IV.8.6}
$$

Since $u_s-2\ge u_s/2$, (IV.7.5) is at most

$$
O_{r,C}\left[
\rho n^{r-1}+R\rho^{-2}n^{r-2}
+R^3\rho^{-6}n^{r-2}\right]
=O_{r,C}(\rho n^{r-1}).
\tag{IV.8.7}
$$

For the equality of orders, divide by $n^{r-1}$ and use $R^3/n=\rho^8$:
$R/(\rho^2n)=\rho^6/R^2\le\rho$ and $R^3/(\rho^6n)=\rho^2\le\rho$.

For facets, (IV.8.1)–(IV.8.3) sum to

$$
O_r\left[R/n+\rho^3+R^3/(\rho^3n)\right]n^{r-1}
=O_r(\rho^3n^{r-1}).
\tag{IV.8.8}
$$

Take the union of all the deletion sets. There are finitely many ranks, and all parent labels and lower-core centers have been fixed before deleting. A shared facet in the final family was shared after the facet cleanup; it retains that same center. This proves all assertions. ∎

### IV.9 Inheritance of centers

We verify the incidence argument passing from Theorem IV.8.1 to the structural proof.

Call $(E,A,a)$ bad if $E\in K_0$, $A\subset E$, $a\in A\setminus\\{z_A\\}$, and $z_{A-a}\ne z_A$. Allow $4\le|A|\le r-2$, and allow $|A|=r-1$ only when $A$ has at least two $K_0$-completions. Thus every center mentioned is defined. Put $\varepsilon=2\rho$ and $\alpha=16\rho$.

For any fixed core size $j$, low-retention cores obey

$$
\sum_{A:d_{K_0}(A)<\alpha d_H(A)}d_{K_0}(A)
\le\alpha\binom rj|H|.
\tag{IV.9.1}
$$

This follows by summing the defining inequality and using
$\sum_{|A|=j}d_H(A)=\binom rj|H|$. The number of bad incidences for which $A$ or $A-a$ has low retention is consequently $O_{r,C}(\rho n^{r-1})$.

For the others, put $B=A-a$, $|B|=k=r-s$, $2\le s\le r-3$, and $R_0=E-B$. A witness consists of two further retained roots $R_1,T$ such that

$$
R_0\cap R_1=\\{a\\},\quad T\cap(R_0\cup R_1)=\varnothing,
$$

$$
c_s(R_0,T)=c_s(R_1,T)=z_B,\qquad
c_{s-1}(R_0-a,R_1-a)=z_A\ne z_B.
\tag{IV.9.2}
$$

The cores and roots are disjoint wherever they must form an edge.

There are at least $d_{K_0}(A)/2$ choices of $R_1$: when $s\ge3$, use the parent-partner guarantee at $A$, losing at most $\varepsilon m_A\le(\varepsilon/\alpha)d_{K_0}(A)$ retained partners; when $s=2$, take any other retained completion of the shared facet, giving $d_{K_0}(A)-1\ge d_{K_0}(A)/2$. The edge $BR_1$ is retained in either case. Both $BR_0$ and $BR_1$ therefore have the partner guarantee at $B$. At most $2\varepsilon m_B$ retained choices fail one of their two guarantees, leaving at least $d_{K_0}(B)/2$ choices of $T$. Each high-retention bad incidence has at least $d_{K_0}(A)d_{K_0}(B)/4$ witnesses.

Count all such witnesses from the other direction. Choose the ordered $(R_0,T)$ in at most $\binom ns^2$ ways; its label $z_B$ is fixed. Choose $a\in R_0$ in at most $s$ ways. By the pinned bound (IV.7.2), at most $D_{s+1}D_{k+1}/t_s$ strong partners $R_1$ of $T$ have that same label and contain $a$. The different upper label $z_A$ is then determined by $R_0-a,R_1-a$. Each possible $B$ contains the two fixed distinct labels and gives an edge $BR_0$ through a fixed $(s+2)$-set, so there are at most $D_{s+2}$ choices. Different bad incidences give different witness tuples, since the tuple recovers $E=BR_0$ and $A=Ba$. It follows that

$$
\sum_{\text{high-retention bad }(E,A,a)}
d_{K_0}(A)d_{K_0}(A-a)
\le4s\binom ns^2\\,\frac{D_{k+1}D_{s+1}D_{s+2}}{t_s}.
\tag{IV.9.3}
$$

Each summand is at least $\alpha^2\rho^2n^{2s-3}$. For lower cores this uses $m_A\ge\rho n^{s-2}$ and $m_B\ge\rho n^{s-1}$. In the facet case $s=2$, use $m_A\ge2\ge\rho$ instead. Substituting the natural bounds and (IV.8.4) in (IV.9.3) therefore bounds the number of high-retention bad incidences by

$$
O_r(R^3\rho^{-7}n^{r-2})=O_r(\rho n^{r-1}).
\tag{IV.9.4}
$$

Delete every edge in any bad incidence, and call the result $L$. Equations (IV.8.5), (IV.9.1) and (IV.9.4) show

$$
|H\setminus L|=O_{r,C}(\rho n^{r-1}).
\tag{IV.9.5}
$$

Every occurring lower core satisfies the inheritance law

$$
z_{A-a}=z_A\qquad(a\ne z_A),
\tag{IV.9.6}
$$

and so does every facet that is still shared in $L$. A facet becoming private causes no problem; no center was ever required on an originally private facet. Parent-partner guarantees for retained edges persist. Finally, if $\sigma(G)=|G|-|\partial G|$, deleting $q$ edges gives

$$
|L|\ge|H|-q,\qquad \sigma(L)\ge\sigma(H)-q,
\tag{IV.9.7}
$$

since $\partial L\subseteq\partial H$. These are the exact conclusions used in §§IV.A–IV.B.

### IV.10 The closing argument

The preceding estimates give a mass-preserving family with the parent labels and inheritance required for the finite root and prefix proof below. We now apply that proof to finish the high-rank theorem.

The root and prefix arguments in §§IV.A–IV.B show that, whenever an admissible parent $H$ satisfies $|H|\le Cn^{r-1}$ and $D_j(H)\le Rn^{r-j-1}$ for $1\le j\le r-1$, with $R\ge1$ and $R^{11}/n\to0$,

$$
\begin{array}{ll}
r\ge6:& |H|=O_{r,C}(\eta n^{r-1}),\\
r=5:& |H|\le\tfrac12|\partial H|+O_C(\eta n^4),
\end{array}
\qquad \eta=(R^{11}/n)^{1/16}\to0.
\tag{IV.10.1}
$$

Sections IV.A–IV.B prove (IV.10.1) using the cleanup and inheritance established in §§IV.7–IV.9.

To see its consequence, fix the near-star radius from Theorem IV.2.1 and choose a fixed $\delta>0$ small enough that $q\le\delta M_n$ implies $q\le\delta_r(n-1)^{r-1}$. If there were arbitrarily large admissible families with $|F|\ge M_n$ outside this near-star radius, Theorem IV.5.3 would give

$$
|H|\ge cn^{r-1},\quad \sigma(H)\ge-o(n^{r-1}),\quad R=\log\log n.
$$

For $r\ge6$ this contradicts the first line of (IV.10.1). For $r=5$, its second line gives $\sigma(H)\le-|H|+o(n^4)$, also a contradiction. Thus every sufficiently large family with $|F|\ge M_n$ lies in that fixed near-star radius. Applying Theorem IV.2.1 yields

$$
g_r(n)=\binom{n-1}{r-1}+\left\lfloor\frac{n-1}{r}\right\rfloor
\qquad(r\ge5,\ n\ \text{sufficiently large}).
\tag{IV.10.2}
$$

The matching-plus-star construction in §IV.2 attains it. The same argument includes equality families, so the two local equality forms in §IV.2.3 also give the global classification.

The finite structural proof of (IV.10.1) follows.

### IV.A. Roots and private facets

The next compatibility lemma completes the face centers at ranks at least six. At rank five it instead counts private facets of unrooted edges.

#### IV.A.1 A finite compatibility lemma

**Lemma IV.A.1 (compatibility of centers).** Let $U\subseteq V$, $|U|\ge4$, $|V\setminus U|\le1$, and let $f:U\to V$ satisfy $f(a)\ne a$ and

$$
f(a)\ne b,\ f(b)\ne a\quad\Longrightarrow\quad f(a)=f(b)
\qquad(a,b\in U,\ a\ne b).
\tag{IV.A.1}
$$

There is a unique $v\in V$ with $f(a)=v$ for every $a\in U\setminus\\{v\\}$.

**Proof.**

Consider the directed function graph. A cycle of length at least four contradicts (IV.A.1) at two vertices two steps apart. A three-cycle $a\to b\to c\to a$ is impossible: any fourth vertex $u\in U$ would satisfy
$f(u)\in\\{a,b\\}\cap\\{b,c\\}\cap\\{c,a\\}=\varnothing$.
If there is a two-cycle $a\leftrightarrow b$, every other vertex points to $a$ or $b$, by comparison with both cycle vertices. Two such vertices cannot point to different endpoints, by (IV.A.1); they therefore all point to a common endpoint $v$, as does the other endpoint. This proves the assertion in this case.

If there is no cycle, the unique possible outside vertex $w\in V\setminus U$ must exist and all paths end there. If every vertex points to $w$, take $v=w$. Otherwise choose a final two-step path $a\to b\to w$. Any $c\in U\setminus\\{a,b\\}$ satisfies
$f(c)\in\\{a,b\\}\cap\\{b,w\\}=\\{b\\}$, so $v=b$ works. Finally two different proposed values of $v$ are excluded by any element of $U$ different from both. ∎

#### IV.A.2 Five vertices

On a five-set $E$, designate $z_S\in S$ for each triple $S$. A four-set $A\subset E$ is coherent if some $w\in A$ satisfies

$$
z_{A-a}=w\qquad(a\in A\setminus\\{w\\}).
\tag{IV.A.2}
$$

That $w$ is unique: a triple containing two proposed centers would have to have both. Call $v\in E$ a root if every triple containing $v$ has center $v$; again a root is unique.

There is a root if and only if at least four of the five four-sets are coherent. A root makes the four four-sets containing it coherent. Conversely, let
$U=\\{a\in E:E-a\text{ is coherent}\\}$ and let $f(a)$ be the center of $E-a$. When $f(a)\ne b$ and $f(b)\ne a$, the shared triple $E-\\{a,b\\}$ has both centers, so (IV.A.1) holds. If $|U|\ge4$, Lemma IV.A.1 gives a vertex $v$. Any triple $S$ containing $v$ omits some $a\in U$; then $a\ne v$ and $S$ lies in the coherent four-set $E-a$ with center $v$. Thus $z_S=v$.

Apply this to $L$ from §IV.9 at rank five. Every shared facet is coherent by inheritance. Hence each edge without a root has at least two noncoherent facets, which must be private. Different edges cannot own the same private facet. If $L_{\rm root}$ is the set of rooted edges,

$$
|\partial L|\ge2|L\setminus L_{\rm root}|,\qquad
|L|\le\tfrac12|\partial L|+|L_{\rm root}|.
\tag{IV.A.3}
$$

#### IV.A.3 Ranks at least six

For any occurring facet $T$ of $L$, define $f(a)=z_{T-a}$ for $a\in T$. The required centers have size $r-2$. If $f(a)\ne b$ and $f(b)\ne a$, inheritance through the common $(r-3)$-core gives $f(a)=f(b)$; here $r-3\ge3$. Lemma IV.A.1 gives a unique center $z_T$ with the required noncenter-deletion inheritance. On shared facets this equals the existing center, by uniqueness. Thus it consistently extends the assignment to private facets.

Use the same lemma on the facets of each edge to define $z_E$. Repeated deletion of vertices other than $z_E$ shows that every subset of that edge of size at least three containing $z_E$ has center $z_E$.

Let $p=r-3$. For $r\ge6$ choose any $p$-set $Y(E)\subset E$ containing $z_E$. Then every $(r-2)$-set $Y(E)x$ has center in $Y(E)$, as does every shared facet $Y(E)xy$. At rank five, for each rooted edge choose its root and any other vertex as its two-set $Y(E)$. Its three-sets $Y(E)x$ have center equal to the root. Every shared facet containing $Y(E)$ has that same center: if its center differed, a triple inside it containing both proposed centers would receive both labels. These are exactly the prefix properties used next.

### IV.B. The prefix bound

Let $K=L$ for $r\ge6$ and $K=L_{\rm root}$ for $r=5$, with the choices of $Y(E)$ from §IV.A. All labels and partner guarantees still refer to the original parent $H$. Put

$$
p=r-3,\quad M=|K|,\quad
D=\Delta_{r-2}(H),\quad D_4=\Delta_4(K),\quad
\varepsilon=2\rho,
$$

$$
N_3=\binom n3,\quad
T_p=\tfrac12\binom np\binom{n-p}p,\quad
B=\max\\{7,1+\varepsilon D\\},\quad
A_0=1+p(D_4-1).
$$

If $M>0$, then $D_4\ge1$. We prove the finite inequality

$$
M^2\le N_3(A_0M+2T_pB).
\tag{IV.B.1}
$$

For each $p$-set $Y$, let $\mathcal H_Y$ consist of the triples $P$ such that $YP\in K$ and the designated prefix of this edge is $Y$. If $Y,Z$ are disjoint, their common triple system $\mathcal C=\mathcal H_Y\cap\mathcal H_Z$ is intersecting: disjoint triples $P,Q$ would give the trade $YP,ZQ$ versus $YQ,ZP$.

It is also linear. Otherwise $abx,aby$ would be two common triples. The shared facet $Yab$ has completions $x,y$ and center in $Y$, so the fixed parent label $c_1(x,y)$ lies in $Y$. The same label lies in $Z$ by the facet $Zab$, contradicting disjointness.

A linear intersecting triple system without a common vertex has at most seven edges. Indeed a vertex on four edges would be common to every edge: an edge avoiding it would have to meet four disjoint two-element petals. Thus its maximum vertex degree is at most three. Fixing one edge, at most two other edges meet each of its three vertices, giving at most $1+3\cdot2=7$ edges.

If instead $\mathcal C=\\{xS_1,\ldots,xS_m\\}$ has a common vertex, its two-set petals $S_i$ are pairwise disjoint. Let $A=Yx$ and $A'=Zx$. Their centers satisfy $z_A\in Y$, hence $z_A\notin A'$. Fix $i$. For each $j\ne i$, both $A$ and $A'$ are parent common cores of the roots $S_i,S_j$. If $S_j$ were a good parent partner for the retained edge $AS_i$ at $A$, its label would be $z_A$, and it would belong to every common core, including $A'$. This is impossible. All $m-1$ other petals are therefore bad partners, giving $m-1\le\varepsilon d_H(A)\le\varepsilon D$. We have proved

$$
|\mathcal H_Y\cap\mathcal H_Z|\le B\qquad(Y\cap Z=\varnothing).
\tag{IV.B.2}
$$

For a triple $P$ let $t_P$ count its assigned prefixes. Each edge is assigned once, so $\sum_Pt_P=M$, and Cauchy–Schwarz gives

$$
\sum_P\binom{t_P}2\ge\tfrac12(M^2/N_3-M).
\tag{IV.B.3}
$$

Among the prefixes for a fixed $P$, any vertex lies in at most $D_4$ of them, since $Pv$ is a four-set contained in the corresponding edges. The number of intersecting prefix pairs is at most

$$
\sum_v\binom{d(v)}2
\le\tfrac12(D_4-1)\sum_vd(v)
=\tfrac12p(D_4-1)t_P.
$$

Summing this bound, and bounding the disjoint prefix pairs by (IV.B.2), yields

$$
\sum_P\binom{t_P}2\le\tfrac12p(D_4-1)M+T_pB.
$$

Together with (IV.B.3), this is (IV.B.1).

Solving the quadratic and using the natural codegrees gives

$$
\begin{aligned}
M&\le A_0N_3+\sqrt{2N_3T_pB}\\
&=O_r\\!\left(Rn^{r-2}+n^{r-3/2}+\sqrt{\rho R}\\,n^{r-1}\right).
\end{aligned}
\tag{IV.B.4}
$$

Since $\sqrt{\rho R}=(R^{11}/n)^{1/16}=\eta$, and $R\ge1$, $R^{11}/n\to0$, each term is $O_r(\eta n^{r-1})$. Also $\rho\le\eta$. Thus (IV.9.5) and (IV.B.4) give

$$
r\ge6:\quad |H|=O_{r,C}(\eta n^{r-1}).
$$

For rank five use (IV.A.3), $\partial L\subseteq\partial H$, and $|H\setminus L|=O_C(\rho n^4)$ to get

$$
r=5:\quad |H|\le\tfrac12|\partial H|+O_C(\eta n^4).
$$

This proves (IV.10.1), and hence (IV.10.2) and its equality classification.

Theorem II.1, Theorem III.1, and (IV.10.2) prove Theorem 1.

## Acknowledgments and AI assistance

OpenAI Codex assisted with proof development, reconstruction of preliminary lemmas, critical review, and manuscript preparation. The named author reviewed the final arguments and takes responsibility for the manuscript.

## References

1. [Erdős Problems, Problem #643](https://www.erdosproblems.com/643).
2. [Justin Sun Prize, JSP-000523](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#jsp-000523).
3. O. Pikhurko and J. Verstraëte, [*The maximum size of hypergraphs without generalized 4-cycles*](https://pikhurko.github.io/E/PikhurkoVerstraete09jcta.pdf), *J. Combin. Theory Ser. A* **116** (2009), 637–649.
