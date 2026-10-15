# 随机 Vandermonde 奇异值估计问题

Full-Vandermonde 定义如下：
$$
V_M=\begin{bmatrix}
1 & 1 & \cdots & 1 \\
e^{2\pi ix_1} & e^{2\pi ix_2} & \cdots & e^{2\pi ix_n}\\
\vdots & \vdots & \ddots & \vdots \\
e^{2\pi iMx_1} & e^{2\pi iMx_2} & \cdots & e^{2\pi iMx_n}
\end{bmatrix}
$$
随机 Vandermonde 就是从 $V_M$ 里面随机抽取一些行，构成一个行数更少的矩阵 $V_{\text{rand}}$。通常有几种设定：

- Bernouli 模型：$V_M$ 的每一行都有 $p$ 的概率保留
- 不放回取样模型：先固定 $m\leq M+1$，从 $V_M$ 里随机抽出 $m$ 个不同的行，每行被抽中的概率相等
- 有放回取样模型：固定 $m\leq M+1$，独立随机抽 $m$ 次，每次都在 $V_M$ 的行里选一行，允许重复选

---

### 1. [Tang 2013](https://arxiv.org/pdf/1207.6053)

#### 1.1 对于 Location Recovery 的估计

本文的 Theorem 1.1 假设无噪音测量：
$$
y_j=\sum_{k=1}^n c_k e^{2\pi i jx_k}
$$
如果在 $y_0,...,y_M$ 中随机知道 $m$ 个无噪音测量的值（**不放回取样**），且已知 $d_{\min}\geq 4/M$，并且
$$
m \geq C\max\left\{\log^2\frac{M}{\eta},n\log \frac{n}{\eta}\log\frac{M}{\eta}\right\},
$$
那么以至少 $1-\eta$ 的概率，可以恢复出所有的 $x_1,...,x_n$。

#### 1.2 对于 random VDM 的奇异值估计

本文的 Lemma 4.4 采用 **Bernouli 模型**，要求 $d_{\min}\geq 4/M$，如果每行保留的概率
$$
p\geq\frac{200n}{M\tau^2}\log\frac{2n}{\eta},
$$
那么，以至少 $1-\eta$ 的概率，对按原文行权重加权后的矩阵，有：
$$
\sqrt{\frac{pM}{4}(0.6377-\tau)}
\leq\sigma_{\min}(V_{\text{rand}}^{\text{带权}})
\leq\sigma_{\max}(V_{\text{rand}}^{\text{带权}})
\leq\sqrt{\frac{pM}{4}(1.3623+\tau)}.
$$
这个结论很容易直接推广到不带权的 $V_\text{rand}$ 上面。

### 2. [Kunis 2006](https://arxiv.org/pdf/math/0604429)

本文的 Thm. 3.3 固定一组互异的格点点源，即 $x_j\in \left\{0,\frac{1}{M+1},\frac{2}{M+1},...,\frac{M}{M+1}\right\}$。用**有放回取样**模型抽取 $m$ 行。对 $0<\delta,\eta<1$，如果
$$
m\geq C\delta^{-2}n\log\frac{n}{\eta},
$$
那么，以至少 $1-\eta$ 的概率，有
$$
\sqrt{m(1-\delta)}
\leq \sigma_{\min}(V_\text{rand})
\leq \sigma_{\max}(V_\text{rand})
\leq \sqrt{m(1+\delta)}.
$$
这是对**预先固定的点源集合**的保证，没有要求同一次抽样对所有格点点源集合同时成立。
