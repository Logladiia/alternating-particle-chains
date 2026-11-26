# 周期 Hölder 求积论文的 Lean 附件

这份独立 Lake 工程对应《样本任意缺失下周期 Hölder 函数的最优求积》。使用 Lean 4.28.0 和锁定版本的 mathlib。

| Lean 定理 | 核验范围 |
| --- | --- |
| `fixed_sample_minimax` | 引理 1 的固定保留点最优误差公式，适用于紧度量空间、非空紧样本集与有限正测度。 |
| `distance_in_lifted_gap`、`gap_integral` | 实轴提升中的最近端点公式及单弧积分常数。 |
| `uniform_quadrature_minimax` | 定理 2 在循环间距模型下的精确极小极大误差，含积分常数。 |
| `uniform_worst_iff`、`consecutive_worst` | 等距网格上，最坏缺失恰对应至多一个含丢点的保留弧。 |
| `unique_of_two_survivors`、`sole_survivor` | 至少保留两点时只有等距设计最优。只保留一点时，所有设计同样最优。 |

若原有 $n$ 个采样点，定义中的 $s=r+1$、$m=n-r-1$。从任一保留点起沿圆周记录各保留弧穿过的原始间隙数，得到一列和为 $n$ 的正整数。反过来，这列数的前缀和给出各保留点的偏移量。圆周点集到循环间距和逐弧积分的整体对应见正文的几何说明。定理 4 与定理 6 的加权渐近结论保留书面证明。

## 复现

安装 Git 和 [elan](https://github.com/leanprover/elan)，进入本目录运行下面的命令。

```sh
lake update
lake exe cache get PeriodicQuadrature.lean
lake build
```

本地已经通过 `lake build`。证明不含 `sorry`。构建会打印关键定理的公理依赖，预期仅有 `propext`、`Classical.choice` 和 `Quot.sound`。如果 Windows 的缓存获取遇到 ProofWidgets 的 tar 编码错误，可在 WSL 或 Linux 中执行同一套命令。
