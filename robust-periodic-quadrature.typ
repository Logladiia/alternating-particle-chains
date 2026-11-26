// Compile with Typst 0.15 or later. No packages, figures, or bibliography files are required.
// If SimSun or Microsoft YaHei is unavailable, select a local CJK font here.
#set document(title: "样本任意缺失下周期 Hölder 函数的最优求积", keywords: ("最优求积", "Hölder 函数", "节点缺失", "标量量化"))
#let serif = ("Libertinus Serif", "SimSun")
#let sans = "Microsoft YaHei"
#set page(paper: "a4", margin: (x: 24mm, top: 23mm, bottom: 22mm),
  header: context { if counter(page).get().first() > 1 { set text(font: serif, size: 8.5pt, fill: luma(95)); [样本任意缺失下周期 Hölder 函数的最优求积 #h(1fr) #line(length: 24mm, stroke: 0.4pt + luma(160))] } },
  numbering: "1", number-align: center)
#set text(font: serif, lang: "zh", region: "CN", size: 11.25pt)
#set par(justify: true, leading: 0.76em, spacing: 0.94em)
#set heading(numbering: "1.")
#show heading.where(level: 1): it => block(above: 1.05em, below: 0.46em, text(font: sans, size: 14.5pt, weight: "bold", it))
#set math.equation(numbering: "(1)")
#show math.equation.where(block: true): set block(above: 0.68em, below: 0.68em)
#let claim(label, title) = text(font: sans, weight: "bold")[#label　#title。]
#let proof = text(weight: "bold")[证明。]
#let qed = box[$square.stroked$]
#let cite(n, lab) = link(lab)[\[#n\]]
#let refline(n, label, body) = block(above: 0.38em, below: 0.38em,
  grid(columns: (1.8em, 1fr), [\[#n\]], [#metadata(n) #label #body]))

#align(center)[
  #text(font: sans, size: 20pt, weight: "bold")[样本任意缺失下周期 Hölder 函数的最优求积]
  #v(2.5pt)
  #text(size: 12pt)[Minimax Quadrature for Periodic Hölder Functions under Sample Erasures]
]
#v(0.75em)
#block(inset: (x: 3mm))[
  *摘要*　对圆周上的 Hölder 半范数单位球，研究从预置的 $N$ 个点值估计加权积分的问题。任意 $r<N$ 个读数可在采样后丢失，求积规则可以使用保留点的位置。均匀权重下，我们给出对所有 $N,r$ 成立的精确极小极大误差，并刻画最优布点。对严格正连续权重和任意 $r=o(N)$，我们给出误差的渐近等价式及一个与删点数无关的渐近最优设计。Hölder 指数为 $alpha$ 时，删点改变误差首项的临界规模为 $N^(1/(1+alpha))$。在此规模以内，任何渐近最优设计在权重分位坐标中的归一化间距与 1 之差的 $1+alpha$ 次绝对矩趋于零。超过此规模后，局部间距可以持续振荡，而采样点的极限密度依然唯一。

  *关键词*　最优求积、Hölder 函数、最优恢复、节点缺失、标量量化
]

= 引言
在一个周期内预先确定采样时刻，若若干读数丢失，剩余观测仍可重新加权。给定剩余点，怎样估计积分才能使最坏误差最小？采样之前，又该如何选择节点才能承受最不利的缺失？圆周上每段无采样弧的误差贡献可以单独求出，从而将这两个问题联系起来。

Mathé #cite(1, <bib-mathe>) 研究了实线上的最优加权求积，其结果包含 Lipschitz 函数的无缺失情形。定点求积与最近点量化的关系可见 Creutzig 等 #cite(2, <bib-dere>)，最优量化误差及渐近点密度的系统理论见 Graf 与 Luschgy #cite(3, <bib-graf>)。Frasca 等 #cite(4, <bib-frasca>) 在一维失效覆盖模型中利用了圆周的循环对称性，其目标是失效后最大覆盖距离的期望。本文对给定数量的所有缺失集合取最大值，误差由距最近保留点的距离幂在整圆上的积分决定。长空弧与其余短弧对该积分的相对贡献，决定何时删点会改变最优求积误差的首项。

= 模型与定点误差
设 $TT=bb(R)\/bb(Z)$ 的周长为 1，$d$ 为短弧距离，$dif x$ 为弧长测度。固定 $0<alpha<=1$，记 $p=1+alpha$、$C_alpha=1/(2^alpha p)$。考虑函数类
$ cal(H)_alpha = { f: TT arrow.r bb(R) | abs(f(x)-f(y)) <= d(x,y)^alpha " 对所有 " x,y in TT }. $
给定连续权重 $w>0$，令 $I_(w)(f)=integral_TT f(x) w(x) dif x$。取含 $N>=1$ 个不同点的设计 $X$，整数 $0<=r<N$。对非空 $S subset.eq X$，以 $e_(w)(S)$ 表示在已知 $S$ 及 $f|_S$ 时，所有确定性算法在 $cal(H)_alpha$ 上的最小最坏绝对误差。定义
$ R_(N,r)(X;w)=max_(S subset.eq X, |S|=N-r) e_(w)(S), quad
  E_(N,r)(w)=inf_(|X|=N) R_(N,r)(X;w). $ <e-model>
算法可随 $S$ 改变。按至多 $r$ 个缺失计算得到相同的值，因为增加已知点不会扩大最优误差。以下涉及点集的下确界均取遍预先固定的不同采样点。

#claim[引理 1][固定保留点的最优误差]
任一非空有限集 $S subset.eq TT$ 满足
$ e_(w)(S)=integral_TT w(x) d(x,S)^alpha dif x. $ <e-fixed>
最优规则是用各保留点 Voronoi 区间的 $w$-质量作为相应读数的系数。

#proof 记 $D(x)=d(x,S)$，把每个 $x$ 指派给一个最近保留点。用该点的读数替代 $f(x)$ 后逐点误差至多为 $D(x)^alpha$，积分给出上界。另一方面，$D$ 为 1-Lipschitz，且非负实数满足 $abs(u^alpha-v^alpha)<=abs(u-v)^alpha$。因此 $plus.minus D^alpha$ 均属于 $cal(H)_alpha$，它们在 $S$ 上的读数完全一致，而积分互为相反数。任何估计值对其中至少一个的误差达到右端。#qed

#pagebreak(weak: true)
= 均匀权重下的精确误差
#claim[定理 2][最优设计与最坏缺失]
令 $s=r+1$。对所有 $N>=1$ 与 $0<=r<N$，
$ E_(N,r)(1)=C_alpha (s^p+N-s)/N^p. $ <e-flat>
等距设计达到该值。若保留至少两个点，最优设计在整体旋转意义下唯一。若只保留一个点，任意设计都最优。在等距设计上，$r>=1$ 时，最坏缺失恰为圆周次序上连续的 $r$ 个点。

#proof 长度为 $h$ 的保留间隙对 @e-fixed 的贡献为 $2 integral_0^(h/2) t^alpha dif t=C_alpha h^p$。此式也适用于只剩一点时首尾重合的整圆间隙。在等距设计上，每个保留间隙含有 $b_j>=0$ 个丢失的点，其长度为 $(1+b_j)/N$，且 $sum_j b_j=r$。由严格凸性，将两个正的 $b_j$ 合并为一个、另一个置零，严格增大 $sum_j (1+b_j)^p$。故连续缺失给出 @e-flat 的上界，并刻画所有极大情形。

对任意设计，按圆周顺序记间隙为 $g_1,...,g_N$，采用循环下标。设
$ z_i=N g_i, quad a_i=1/s sum_(j=0)^(s-1) z_(i+j), quad M_(p)(v)=1/N sum_(i=1)^N v_i^p. $ <e-moment>
两列 $z,a$ 的平均值均为 1。取一段由 $s$ 个原始间隙组成的长弧，删去其内部 $s-1$ 个点。长弧长为 $s a_i/N$。对长弧的 $N$ 个起点取平均，每个原始间隙作为单独保留间隙恰出现 $N-s$ 次。最大风险至少为这 $N$ 种情形的平均值，故
$ R_(N,r)(X;1) >= C_alpha/N^p [s^p M_(p)(a)+(N-s)M_(p)(z)]. $ <e-stability>
Jensen 不等式给出 $M_(p)(a),M_(p)(z)>=1$，与上界相合。若 $N-s>0$，达到下界强制 $M_(p)(z)=1$，严格凸性给出 $z_i=1$ 对所有 $i$ 成立。若 $s=N$，唯一保留间隙长为 1，代价恒为 $C_alpha$。#qed

= 正权重与临界规模
令 $w_* = min_TT w>0$。固定圆上一点为原点，在实线上取周期延拓，定义
$ A=integral_0^1 w(t)^(1/p) dif t, quad
 F(x)=1/A integral_0^x w(t)^(1/p) dif t, quad F(x+1)=F(x)+1. $ <e-transform>
该映射在圆周上保序，并且双向 Lipschitz。用 $Y_N$ 表示 $N$ 个等距点，令 $X_N^*=F^(-1)(Y_N)$。为说明渐近中的一致性，设
$ omega(h)=sup_(d(x,y)<=h) abs(log w(x)- log w(y)). $
这里 $h>=0$，由连续性有 $omega(h) arrow.r 0$ 当 $h arrow.r 0$。

#claim[引理 3][单个间隙的比较]
设 $I$ 是保留点之间的有向间隙，原长为 $h$、经 $F$ 变换后长为 $q$。记其对 @e-fixed 的贡献为 $J_(w)(I)$。则
$ e^(-omega(h)) C_alpha A^p q^p <= J_(w)(I) <= e^(omega(h)) C_alpha A^p q^p. $ <e-local>

#proof 令 $m_I,M_I$ 为弧上权重的最小、最大值。由引理 1 和均匀间隙积分，$J_(w)(I)$ 介于 $C_alpha m_I h^p$ 与 $C_alpha M_I h^p$ 之间。由 $A q=integral_I w^(1/p) dif x$，$C_alpha A^p q^p$ 也介于同一对端点之间。两端之比至多为 $exp(omega(h))$。#qed

#claim[定理 4][加权误差]
对任意整数序列 $r=r_N=o(N)$，有
$ R_(N,r)(X_N^*;w) tilde E_(N,r)(w) tilde
  C_alpha A^p ((r+1)^p+N-r-1)/N^p. $ <e-weighted>
符号 $tilde$ 指比值趋于 1。同一设计序列 $X_N^*$ 适用于所有这些删点预算。

#pagebreak(weak: true)
#proof 以下估计同时给出有限 $N$ 下的界。记 $V=E_(N,r)(1)$、$s=r+1$，并设
$ h_+ = min(1, (A s)/(w_*^(1/p) N)), quad
 U=A^p V exp(omega(h_+)), quad
 h_- = min(1, (U/(C_alpha w_*))^(1/p)). $ <e-scales>
在 $X_N^*$ 中，任意缺失之后的新坐标间隙至多为 $s/N$，由 @e-transform，相应原长至多为 $h_+$。对所有保留间隙求和并应用 @e-local 与定理 2，可知该设计的风险至多为 $U$。

若设计的风险至多为 $U$，其每一种缺失情形下的每一个间隙都满足 $C_alpha w_* h^p<=U$，故 $h<=h_-$。用 @e-local 的下界逐段求和，再对缺失集合取最大值，给出风险下界 $A^p exp(-omega(h_-))R_(N,r)(F(X);1)$。它至少为 $A^p exp(-omega(h_-))V$。风险大于 $U$ 的设计也满足后一界。因此
$ A^p V exp(-omega(h_-)) <= E_(N,r)(w) <= R_(N,r)(X_N^*;w) <= U. $ <e-twosided>
当 $r=o(N)$ 时，$h_+ arrow.r 0$ 且 $V arrow.r 0$，故 $U,h_- arrow.r 0$。两端之比趋于 1。#qed

#claim[推论 5][三个删点尺度]
若 $r/N^(1/p) arrow.r c in [0,infinity)$，则 $frac(E_(N,r)(w), E_(N,0)(w)) arrow.r 1+c^p$。若 $r/N^(1/p) arrow.r infinity$ 且 $r=o(N)$，则 $E_(N,r)(w) tilde C_alpha A^p (r/N)^p$。

#proof 将 @e-weighted 分别用于 $r$ 与 0。两者之比渐近等于 $1+((r+1)^p-r-1)/N$，两项的相对大小给出所述极限。#qed

例如，当 $alpha=1$、$w=1$ 时，有 $E_(N,r)(1)=1/(4N)+frac(r(r+1),4N^2)$。在 $N=100$ 时，删去 10 个读数使最优误差从 $1/400$ 上升为 $21/4000$，倍率恰为 $2.1$。固定删去 10 个点并令 $N$ 增大，则该倍率趋于 1。

一个非均匀的例子可直接看出节点如何移动。取 $alpha=1$，令 $w(x)=(1+epsilon cos(2 pi x))^2/(1+epsilon^2/2)$，其中 $0<epsilon<1$。此权重的积分为 1，且
$ F(x)=x+frac(epsilon,2 pi)sin(2 pi x), quad A^2=frac(1,1+epsilon^2/2). $
故只需在每个周期解 $F(x_j)=j/N$，即得到适用于所有 $r=o(N)$ 的渐近最优节点。权重最高处与最低处的渐近节点密度之比为 $(1+epsilon)/(1-epsilon)$。

= 渐近最优设计的间距与点密度
设 $r=o(N)$。称 $X_N$ 渐近最优，如果 $frac(R_(N,r)(X_N;w), E_(N,r)(w)) arrow.r 1$。以下所有间距均在 $F$ 坐标中测量。令 $g_i$ 为 $F(X_N)$ 的相邻间距，$z_i,a_i$ 定义如 @e-moment。其中 $a_i$ 是从第 $i$ 个间隙起连续 $s$ 个归一化间距的算术平均。

#claim[定理 6][极限点密度与局部间距]
对任一渐近最优序列与 $s=r+1$，有
$ 1/N sum_(i=1)^N abs(a_i-1)^p arrow.r 0, quad
  1/N sum_(x in X_N) delta_x arrow.r^("弱") (w(x)^(1/p))/A dif x. $ <e-density>
其中 $delta_x$ 是单位点质量。若另有 $r=O(N^(1/p))$，则
$ 1/N sum_(i=1)^N abs(z_i-1)^p arrow.r 0. $ <e-gap>
当 $r/N^(1/p) arrow.r infinity$ 且 $r=o(N)$ 时，还必有 $max_i a_i arrow.r 1$，但存在渐近最优设计使 @e-gap 的左端趋于一个严格正的常数。

#proof 先说明均匀权重的估计适用于变换后的设计。由定理 4，渐近最优设计的风险趋于零。其任何保留间隙的原长 $h$ 都满足 $C_alpha w_* h^p<=R_(N,r)(X_N;w)$，故对所有删法有 $h=o(1)$，且该估计一致。由 @e-local 求和并取最大值，
$ R_(N,r)(X_N;w)=(1+o(1)) A^p R_(N,r)(F(X_N);1). $ <e-transfer>
#pagebreak(weak: true)
所以 $F(X_N)$ 对均匀权重渐近最优。结合 @e-stability 与 @e-flat，有
$ (s^p (M_(p)(a)-1)+(N-s)(M_(p)(z)-1))/(s^p+N-s) arrow.r 0. $ <e-excess>
逐窗使用 Jensen 不等式再平均，得 $1<= M_(p)(a)<=M_(p)(z)$。因此 @e-excess 总能推出 $M_(p)(a) arrow.r 1$。当 $r=O(N^(1/p))$ 时，$(N-s)/(s^p+N-s)$ 有严格正的下界（对充分大 $N$），故 $M_(p)(z) arrow.r 1$。

对任一非负、均值为 1 的有限列 $v$，令 $psi(t)=t^p-1-p(t-1)$。列 $psi(v_i)$ 的平均为 $M_(p)(v)-1$。每个 $epsilon>0$ 对应常数 $K_epsilon<infinity$，使 $abs(t-1)^p<=K_epsilon psi(t)$ 在 $t>=0$、$abs(t-1)>=epsilon$ 时成立：严格凸性给出有界闭区间上的界，而当 $t arrow.r infinity$ 时两端函数之比趋于 1。在其余区域 $abs(t-1)^p<=epsilon^p$。因此 $M_(p)(v) arrow.r 1$ 蕴含 $N^(-1) sum_i abs(v_i-1)^p arrow.r 0$。这给出 @e-density 的第一式及 @e-gap。

为得点密度结论，在实线上按顺序提升变换后的点 $y_i$，使 $y_(i+N)=y_i+1$。设 $u_i=s^(-1)sum_(j=0)^(s-1)y_(i+j)$，则 $u_(i+1)-u_i=a_i/N$。由 Hölder 不等式，$N^(-1)sum_i abs(a_i-1) arrow.r 0$。望远镜求和给出
$ max_(0<=k<N) abs(u_(1+k)-u_1-k/N) arrow.r 0. $
同时 $0<=u_i-y_i<=y_(i+s)-y_i$，右端是一种连续删点所产生的保留弧长，在原坐标中一致趋零，在 Lipschitz 映射 $F$ 下亦然。因此 $y_(1+k)=y_1+k/N+o(1)$ 对 $k$ 一致成立。平移等距网格对任意连续周期测试函数的 Riemann 和一致收敛，故变换后点集的经验测度弱收敛到弧长测度。经 $F^(-1)$ 拉回即得 @e-density。

在超临界情形，删去任一 $s$ 段窗口的内部节点，仅此窗口便产生均匀权重代价 $C_alpha (s a_i/N)^p$。结合渐近最优性和 @e-flat，得 $(max_i a_i)^p <= (1+o(1))(1+(N-s)/s^p) arrow.r 1$。又因 $a_i$ 的均值为 1，所称最大值极限成立。

最后构造超临界情形的反例。固定 $0<eta<1$，先取偶数 $N$，在新坐标中令 $z_i=1+(-1)^i eta$。任意包含 $k$ 个原始间隙的弧，其长度至多为 $(k+eta)/N$。把各保留弧的原始间隙数写为 $k_j=1+b_j$，其中 $sum_j b_j=r$。与定理 2 相同的凸性论证给出
$ R_(N,r)(F(X_N);1) <= C_alpha/N^p [(s+eta)^p+(N-s)(1+eta)^p]. $ <e-counter>
当 $s^p/N arrow.r infinity$ 时，右端与 @e-flat 之比趋于 1，且变换坐标中的最长保留弧至多为 $(s+eta)/N=o(1)$。由引理 3，取逆像得到所需的加权渐近最优设计，但单间距偏差的 $p$ 次均值恒为 $eta^p$。若要求逐个整数 $N$ 取设计，对奇数 $N$ 交替排列前 $N-1$ 个间距，末项取 $z_N=1$。任何循环块的正负偏差和的绝对值仍至多为 $eta$，故同一估计成立，偏差均值趋于 $eta^p$。#qed

= 讨论
在 $r=o(N)$ 下，密度 $w^(1/p)/A$ 同时解决无缺失时的布点问题和含长缺失弧时的一阶布点问题。定理 6 说明，临界尺度还区分了采样设计的两种行为。误差仍约束平均点密度，而超过该尺度后，达到首项精度容许持久的相邻间距振荡。

均匀权重的精确式覆盖所有 $r<N$。对于一般权重，若 $r/N$ 趋于严格正的常数，最坏缺失弧在极限中可以保持正长度，引理 3 的局部比较不再产生趋零的相对误差。此时该如何从整段弧上的权重分布求出最优设计，是一个独立的变分问题。

#heading(numbering: none)[参考文献]
#set text(size: 9.5pt)
#set par(leading: 0.45em)
#refline(1, <bib-mathe>)[P. Mathé. Asymptotically optimal weighted numerical integration. _Journal of Complexity_ *14* (1998), 34–48. #link("https://doi.org/10.1006/jcom.1997.0467")[doi:10.1006/jcom.1997.0467].]
#refline(2, <bib-dere>)[J. Creutzig, S. Dereich, T. Müller-Gronbach and K. Ritter. Infinite-dimensional quadrature and approximation of distributions. _Foundations of Computational Mathematics_ *9* (2009), 391–429. #link("https://doi.org/10.1007/s10208-008-9029-x")[doi:10.1007/s10208-008-9029-x].]
#refline(3, <bib-graf>)[S. Graf and H. Luschgy. _Foundations of Quantization for Probability Distributions_. Lecture Notes in Mathematics 1730, Springer, Berlin, 2000. #link("https://doi.org/10.1007/BFb0103945")[doi:10.1007/BFb0103945].]
#refline(4, <bib-frasca>)[P. Frasca, F. Garin, B. Gerencsér and J. M. Hendrickx. Optimal one-dimensional coverage by unreliable sensors. _SIAM Journal on Control and Optimization_ *53* (2015), 3120–3140. #link("https://doi.org/10.1137/140968094")[doi:10.1137/140968094].]
