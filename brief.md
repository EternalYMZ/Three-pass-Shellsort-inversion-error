# 从一个键看清末遍的逆序

前两遍间隔为正整数 $h,g$，且 $\gcd(h,g)=1$。排完这两遍之后，每条 $g$ 链都已升序。固定一个键 $x$ 和一条 $g$ 链。链上比 $x$ 小的键占一个前缀，位置在 $x$ 左边的槽也占一个前缀。两个前缀长度相差多少，这条链就有多少键与 $x$ 形成逆序。这里先对单个输入计数，无须指定概率分布。

怎样从第一遍之前的数组读出这个差？在每条 $h$ 链 $s$ 中数出比 $x$ 小的键数 $b_s$。第一遍排好后，该前缀的下一个位置是 $s+hb_s$，可按模 $g$ 记录。让 $j$ 表示 $x$ 第一遍之后所在位置模 $g$ 的余数。从 $j$ 起，每次加 $h$ 再取模，走 $\ell$ 步，$0\le\ell<g$。互素性保证这 $\ell$ 个落点互异。记落在这些点上的其他 $h$ 链前缀端点数为 $Q_{x,\ell}$，每条链单独计一次。

比较起点与终点对应的两条 $g$ 链上的前缀计数时，沿途的项依次抵消，只留下前缀端点和一个确定的取整项。于是，终点对应的链与 $x$ 形成的逆序数恰为 $|Q_{x,\ell}-\lfloor h\ell/g\rfloor|$。让 $\ell$ 取遍各值，再对 $x$ 求和，每个逆序在两个端点各被算一次。若 $M_3$ 是末遍成功右移数，便有

$$
2M_3=\sum_x\sum_{\ell=0}^{g-1}|Q_{x,\ell}-\lfloor h\ell/g\rfloor|.
$$

Lean 已验证这条逐输入恒等式。要和 Janson–Knuth 的均值主项 $n\psi(h,g)$ 比较，还须控制均匀随机输入下真实端点分布与参考分布的差。这一步的绝对误差估计已有解析推导，尚待形式化。对一般互素间隔，无附加误差的单侧均值猜想仍开放。[端点抵消](https://github.com/EternalYMZ/Three-pass-Shellsort-inversion-error/blob/afe8a5e00022093474444bc1d3b6aebc3481a940/Shellsort/PivotArcEndpoints.lean) · [末遍实际右移数](https://github.com/EternalYMZ/Three-pass-Shellsort-inversion-error/blob/afe8a5e00022093474444bc1d3b6aebc3481a940/Shellsort/PivotArcCostBridge.lean)
