# Matrix Chernoff 与加权抽样

**引理（Matrix Chernoff，无放回抽样）。** 设 $q,N\ge1$ 为整数，$b>0$，且 $\mathbf A_1,\ldots,\mathbf A_N\in\mathbb C^{q\times q}$ 是 Hermitian 矩阵，满足

$$
0\le\lambda_{\min}(\mathbf A_k)\le\lambda_{\max}(\mathbf A_k)\le b,
\qquad
\mu:=\lambda_{\min}\!\left(\frac1N\sum_{k=1}^N\mathbf A_k\right)>0.
$$

若 $\mathcal W$ 是均匀选取的 $m$-元子集，其中 $1\le m\le N$，则对 $0<u<1$，

$$
\mathbb P\!\left\{
\lambda_{\min}\!\left(\frac1m\sum_{k\in\mathcal W}\mathbf A_k\right)
\le(1-u)\mu
\right\}
\le q\exp\!\left[
-\frac{m\mu}{b}\bigl(u+(1-u)\log(1-u)\bigr)
\right].
$$

---

证明 Thm 4.6 的主要想法，就是把样本矩阵的最小奇异值写成上述样本平均矩阵的最小特征值，再应用这个引理。需要检查的两个量是单项上界 $b$ 和平均矩阵的最小特征值 $\mu$；概率估计取决于它们的比值 $\mu/b$。

令

$$
\Gamma_L=\{0,\ldots,L\}^d,\qquad N=(L+1)^d,\qquad
\mathbf V=\mathcal V_{\Gamma_L}(\mathcal X),\qquad
\mathbf G=\frac1N\mathbf V^*\mathbf V.
$$

以下取 $0<\rho,\epsilon<1$，令 $\mathcal W\subset\Gamma_L$ 为均匀选取的 $m$-元子集，其中 $n\le m\le N$，并记 $\mathbf V_{\mathcal W}=\mathcal V_{\mathcal W}(\mathcal X)$。

完整网格的确定性估计保证 $\mathbf G$ 正定。沿用正文的定义

$$
\mathbf f(\mathbf k)
=\mathbf G^{-1/2}
[e^{-i\mathbf k\cdot\mathbf y_1},\ldots,e^{-i\mathbf k\cdot\mathbf y_n}]^\top,
\qquad
\frac1N\sum_{\mathbf k\in\Gamma_L}\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*
=\mathbf I.
$$

先直接使用原始 Vandermonde 行，取

$$
\mathbf A_{\mathbf k}
=\mathbf G^{1/2}\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*\mathbf G^{1/2}.
$$

这些矩阵的平均值及单项最大特征值为

$$
\frac1N\sum_{\mathbf k\in\Gamma_L}\mathbf A_{\mathbf k}=\mathbf G,
\qquad
\lambda_{\max}(\mathbf A_{\mathbf k})
=\|\mathbf G^{1/2}\mathbf f(\mathbf k)\|_2^2=n.
$$

因此 Chernoff 引理中的参数是

$$
q=n,\qquad b=n,\qquad \mu=\lambda_{\min}(\mathbf G).
$$

取 $u=\rho$，并利用

$$
\rho+(1-\rho)\log(1-\rho)
=\int_0^\rho-\log(1-s)\,ds
\ge\int_0^\rho s\,ds=\frac{\rho^2}{2},
$$

得到

$$
\mathbb P\!\left\{
\sigma_{\min}(m^{-1/2}\mathbf V_{\mathcal W})^2
\le(1-\rho)\lambda_{\min}(\mathbf G)
\right\}
\le n\exp\!\left[-\frac{m\rho^2\lambda_{\min}(\mathbf G)}{2n}\right].
$$

所以充分条件

$$
m\ge\frac{2n}{\rho^2\lambda_{\min}(\mathbf G)}\log\frac n\epsilon
$$

保证，以至少 $1-\epsilon$ 的概率，

$$
\sigma_{\min}(m^{-1/2}\mathbf V_{\mathcal W})
\ge\sqrt{1-\rho}\,\sigma_{\min}(N^{-1/2}\mathbf V).
$$

**问题在于这个抽样条件含有 $1/\lambda_{\min}(\mathbf G)$。**

---

再考虑取

$$
\mathbf A_{\mathbf k}=\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*.
$$

这时平均矩阵为 $\mathbf I$，所以 $\mu=1$，但单项上界变成

$$
b=\max_{\mathbf k\in\Gamma_L}\|\mathbf f(\mathbf k)\|_2^2.
$$

正文已有的估计是 $b\le K^2n$，其中 $K=2^{4dn^2}$。于是同样的计算只能保证在

$$
m\ge\frac{2K^2n}{\rho^2}\log\frac n\epsilon
$$

时得到所需结论。这个条件已经不含节点间距，但仍然比正文的

$$
m\ge\frac{3n}{\rho^2}\log\frac n\epsilon
$$

强得多。

---

因此考虑权重 $0<w_{\mathbf k}\le1$，并令

$$
\mathbf B:=\frac1N\sum_{\mathbf k\in\Gamma_L}
w_{\mathbf k}\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*.
$$

若能使 $\mathbf B$ 正定，就可以取

$$
\mathbf A_{\mathbf k}
=w_{\mathbf k}\mathbf B^{-1/2}
\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*\mathbf B^{-1/2}.
$$

此时

$$
\frac1N\sum_{\mathbf k\in\Gamma_L}\mathbf A_{\mathbf k}
=\mathbf B^{-1/2}\mathbf B\mathbf B^{-1/2}
=\mathbf I,
\qquad
\lambda_{\max}(\mathbf A_{\mathbf k})
=w_{\mathbf k}\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k).
$$

所以需要同时证明

$$
\lambda_{\min}(\mathbf B)\ge\delta>0,
\qquad
w_{\mathbf k}\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)
\le\frac52n,
$$

其中 $\delta$ 只依赖 $d,n$。

这说明正文为什么考虑

$$
R=\frac{12n}{5},
\qquad
w_{\mathbf k}
=\frac{R}{R+\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)}.
$$

只要这样的 $\mathbf B$ 满足前面的平均等式，就立即有

$$
\lambda_{\max}(\mathbf A_{\mathbf k})
=
\frac{R\,\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)}
{R+\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)}
\le R=\frac{12n}{5}\le\frac52n.
$$

此时 Chernoff 的参数成为 $\mu=1$、$b=5n/2$，概率指数中不再出现 $\lambda_{\min}(\mathbf G)$ 或 $K^2$。

权重还允许把所得下界传回无权重样本。具体地，若样本满足

$$
\lambda_{\min}\!\left(\frac1m\sum_{\mathbf k\in\mathcal W}\mathbf A_{\mathbf k}\right)\ge1-u,
$$

那么对任意 $\mathbf a\in\mathbb C^n$，

$$
\begin{aligned}
\frac{\|\mathbf V_{\mathcal W}\mathbf a\|_2^2}{m}
&=\frac1m\sum_{\mathbf k\in\mathcal W}
|\mathbf f(\mathbf k)^*\mathbf G^{1/2}\mathbf a|^2\\
&\ge\frac1m\sum_{\mathbf k\in\mathcal W}
w_{\mathbf k}|\mathbf f(\mathbf k)^*\mathbf G^{1/2}\mathbf a|^2\\
&=(\mathbf B^{1/2}\mathbf G^{1/2}\mathbf a)^*
\left(\frac1m\sum_{\mathbf k\in\mathcal W}\mathbf A_{\mathbf k}\right)
(\mathbf B^{1/2}\mathbf G^{1/2}\mathbf a)\\
&\ge(1-u)\|\mathbf B^{1/2}\mathbf G^{1/2}\mathbf a\|_2^2\\
&\ge(1-u)\delta\|\mathbf G^{1/2}\mathbf a\|_2^2
=\frac{(1-u)\delta}{N}\|\mathbf V\mathbf a\|_2^2.
\end{aligned}
$$

因此

$$
\sigma_{\min}(m^{-1/2}\mathbf V_{\mathcal W})
\ge\sqrt{(1-u)\delta}\,\sigma_{\min}(N^{-1/2}\mathbf V).
$$

完整证明还必须给出满足这些条件的 $\mathbf B$，并证明其最小特征值有上述正下界。这正是正文中对 $\Psi$ 作极小化、再利用一阶导数等式所完成的确定性部分。

---

## 从矩阵方程反推一阶条件

这个构造有明确的文献先例。一阶条件可以从所需的矩阵方程反推出来：先选取能控制单项大小的权重，再把待求方程中的各项写成某个目标函数的导数。

按前文的公式顺序，(17)、(18) 的关键要求是

$$
\mathbf B=\frac1N\sum_{\mathbf k\in\Gamma_L}
w_{\mathbf k}\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*.
$$

只要这个等式成立且 $\mathbf B$ 正定，(17) 中定义的矩阵就自动满足平均值为 $\mathbf I$。因此，真正需要选的是权重，使这个等式与 (21) 的单项上界同时成立。

(21) 要控制的量是

$$
w_{\mathbf k}\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k).
$$

为了让它有统一上界，考虑

$$
w_{\mathbf k}
=\frac{R}{R+\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)}.
$$

这样立即有

$$
w_{\mathbf k}\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)
=
\frac{R\,\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)}
{R+\mathbf f(\mathbf k)^*\mathbf B^{-1}\mathbf f(\mathbf k)}
\le R.
$$

这个选择并不唯一；它的便利之处是，上界直接成立，而且这个权重有简单的原函数。

现在把它代回平均等式。令 $\mathbf A=\mathbf B^{-1}$，需要求解的方程变成

$$
\boxed{
\mathbf A^{-1}
=\frac1N\sum_{\mathbf k\in\Gamma_L}
\frac{R}{R+\mathbf f(\mathbf k)^*\mathbf A\mathbf f(\mathbf k)}
\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*.
}
$$

就是从这个方程，可以想到一阶条件。两边分别对应以下两项的导数，其中 $\mathbf H$ 是任意 Hermitian 矩阵：

$$
D(-\log\det\mathbf A)[\mathbf H]
=-\operatorname{tr}(\mathbf A^{-1}\mathbf H),
$$

以及

$$
\begin{aligned}
&D\!\left[
R\log\!\left(1+\frac{\mathbf f(\mathbf k)^*\mathbf A\mathbf f(\mathbf k)}R\right)
\right][\mathbf H]\\
&\qquad=
\frac{R}{R+\mathbf f(\mathbf k)^*\mathbf A\mathbf f(\mathbf k)}
\operatorname{tr}\!\left(\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*\mathbf H\right).
\end{aligned}
$$

后一项中的对数，是把所需权重积分得到的：

$$
\int_0^t\frac{R}{R+s}\,ds=R\log(1+t/R).
$$

因此定义

$$
\Psi(\mathbf A)
=-\log\det\mathbf A
+\frac RN\sum_{\mathbf k\in\Gamma_L}
\log\!\left(1+\frac{\mathbf f(\mathbf k)^*\mathbf A\mathbf f(\mathbf k)}R\right),
$$

便有

$$
D\Psi(\mathbf A)[\mathbf H]
=
\operatorname{tr}\!\left[
\left(
-\mathbf A^{-1}
+\frac1N\sum_{\mathbf k\in\Gamma_L}
\frac{R\,\mathbf f(\mathbf k)\mathbf f(\mathbf k)^*}
{R+\mathbf f(\mathbf k)^*\mathbf A\mathbf f(\mathbf k)}
\right)\mathbf H
\right].
$$

它对所有 Hermitian 方向 $\mathbf H$ 都等于零，恰好就是上面要解的矩阵方程。

因此，这个联想的具体顺序是：

1. 从 (21) 选一个能控制单项大小的权重。
2. 代回 (18) 所需的平均等式，得到关于 $\mathbf B$ 的非线性方程。
3. 换成 $\mathbf A=\mathbf B^{-1}$，把方程中的两项分别写成导数。
4. 得到 $\Psi$，再证明它存在极小点。

## 文献中的对应关系

**Maronna（1976）** 的 *Robust M-Estimators of Multivariate Location and Scatter*，已经研究形如

$$
\mathbf B=\frac1N\sum_{k=1}^N
u(\mathbf x_k^\top\mathbf B^{-1}\mathbf x_k)\,
\mathbf x_k\mathbf x_k^\top
$$

的矩阵方程，即权重依赖于待求矩阵本身。参见[原始论文](https://doi.org/10.1214/aos/1176343347)。

**Dümbgen、Pauly、Schweizer（2015）** 的 *M-functionals of multivariate scatter* 可以直接对照。Definition 4.1 定义“$\log\det\mathbf B$ 加上二次型损失的平均值”；Theorem 4.9 和 Corollary 5.3 明确把相应矩阵方程与一阶条件联系起来。取其损失函数为

$$
\rho(t)=R\log(1+t/R)
$$

后，目标函数就是这里的 $\Psi(\mathbf B^{-1})$，相差的仅是与 $\mathbf B$ 无关的常数。这是把本文公式代入该框架得到的对应。参见 [Definition 4.1](https://arxiv.org/pdf/1312.5594#page=14)、[Theorem 4.9](https://arxiv.org/pdf/1312.5594#page=17)、[Corollary 5.3](https://arxiv.org/pdf/1312.5594#page=23)。

**复数向量也有对应文献。** Couillet、Pascal、Silverstein 的 *The Random Matrix Regime of Maronna's M-estimator with elliptically distributed samples* 在式 (1) 中直接使用复数向量及共轭转置，写出同类矩阵方程。参见[式 (1)](https://arxiv.org/pdf/1311.7034#page=3)。

这些资料给出了这个变分构造的明确先例。对本文而言，仍需利用 Vandermonde 的性质证明 $\Psi$ 确实存在极小点，并得到仅依赖 $d,n$ 的 $\lambda_{\min}(\mathbf B)$ 下界；把方程写成 first-order condition 本身还不能保证这两件事。
