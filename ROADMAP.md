# crabsat ロードマップ

kissat (v4.0.4, MIT) の設計を参照した、Rust 製の高性能 CDCL SAT ソルバ。

## 設計原則

1. **メモリレイアウト優先** — 節アリーナ (u32 オフセット参照)、2リテラル節は watch のみ、
   リテラル添字の値配列、詰めた watch 表現。後から変えにくい部分を最初に固める。
2. **常に検証可能** — すべてのフェーズで DRAT 証明を出力し、SAT はモデル検証、UNSAT は
   drat-trim で検証する。kissat を差分テストのオラクルとして使う。
3. **ticks による予算管理** — 探索中にキャッシュライン単位のアクセス量 (ticks) を数え、
   モード切替や inprocessing の予算をそれに比例させる。
4. **unsafe は局所化** — 境界チェック除去は propagate / analyze / arena に限定し、
   `debug_assert!` で常に守る。

## マイルストーン

各マイルストーンの完了条件 (DoD) を満たしたら次へ進む。

### M0: 基盤

- [x] Cargo プロジェクト、release プロファイル (lto=fat, codegen-units=1, panic=abort)
- [x] 型: `Lit`, `Var`, `CRef`、`Value` (i8)
- [x] DIMACS パーサ (xz/gz/bz2 は外部ツールで展開)
- [x] SAT competition 形式の出力 (`s SATISFIABLE` / `v ...` / exit code 10/20)
- [x] DRAT 証明出力 (テキスト / バイナリ)
- [x] テスト基盤 (`scripts/fuzz.py`, `tests/basic.rs`): ランダム CNF 生成、モデル検証、drat-trim 連携、kissat 差分テスト

### M1: CDCL コア (MiniSat 相当)

- [x] 節アリーナ: ヘッダ (glue, used, flags, searched, size) + リテラル
- [x] 2リテラル節は watch のみ (virtual binary)
- [x] watch: Kissat と同じ 32bit 可変長形式 (binary 1語 / large 2語)
- [x] 伝播: kissat 方式 (`lits[0]^lits[1]^not_lit`、searched 位置、delayed watches)
- [x] 1UIP 解析、再帰的 minimization (poison/removable)
- [x] VSIDS (二分ヒープ, f64 スコア, rescale)
- [x] 学習節削減 (glue + used)
- [x] restart (glue EMA)、phase saving
- **DoD**: ランダム 3-SAT / fuzz 1万件で kissat と結果一致、UNSAT 証明が全て検証可能

### M2: kissat 探索コア

- [x] VMTF キュー (focused モード)、enqueue stamp、bump の stamp 順ソート
- [x] stable/focused モード切替 (focused: 衝突数、stable: ticks、nlog⁴n 間隔)
- [x] focused restart: fast/slow glue EMA (bias 補正付き) + margin
- [x] stable restart: reluctant doubling (Luby)
- [x] target / best phase、rephasing (best / original / inverted; walk は未実装で best に置換)
- [x] chronological backtracking (chronolevels=100)
- [x] shrinking (kissat の block 単位 all-UIP 短縮、shrink=3)
- [x] reason-side bumping (decision rate 制限付き)
- [x] tier1/tier2 動的計算と reduce (used カウンタ、reducehigh/low)
- [x] OTFS (on-the-fly strengthening)
- [x] eager subsumption
- [x] restart 時の trail 再利用
- [x] 統計出力 (`c` 行)
- **DoD**: SAT Competition 2023 のサブセットで inprocessing 無効の kissat
  (`--simplify=false` 系) と同等程度の PAR-2

### M3: 基本 inprocessing

- [x] ticks ベースのスケジューラ (effort per mille, mineffort)
- [x] ガベージコレクション (アリーナのコンパクション)
- [ ] compact (変数の振り直し)
- [x] probing: failed literal (2リテラル節の根から)
- [x] substitute: 2リテラル節の SCC による等価リテラル置換
- [ ] transitive reduction
- [x] vivification (tier1/tier2/tier3/irredundant)
- [x] subsumption / strengthening (forward, one-watch)
- [x] BVE: bounded variable elimination + ゲート検出 (AND / 等価 / ITE、XOR は既定で無効)
- [ ] 定義抽出 (kitten)
- [x] モデル復元 (extension stack)
- [x] transitive reduction
- [ ] backbone
- **DoD**: kissat デフォルトの 70〜80% 程度の解けた問題数

### M4: 高度な技法

- [x] walk (ProbSAT) による rephasing
- [x] lucky phases、warmup
- [x] kitten (小さな内部ソルバ) と SAT sweeping (backbone + 分割精緻化による同値検出)
- [ ] kitten による定義抽出 (BVE)
- [x] congruence closure (AND / ITE / XOR、RUP 証明付き)
- [x] factor (bounded variable addition) — M3 で前倒し実装
- [x] xz/gz 圧縮入力

- [x] decision reordering (reorder)、random decision sequences (randec)

### M5: 差別化

- [ ] IPASIR 互換の増分 API (assumptions)
- [x] 並列ポートフォリオ (`--threads=N`、root unit の共有)
- [ ] 節共有の拡張 (2リテラル節、低 glue 学習節)

## ベンチマーク方針

- SAT Competition 2023 main track から、kissat が 1〜60 秒で解ける問題をサブセットとして選ぶ。
- `scripts/bench.sh` で crabsat と kissat を同条件 (タイムアウト付き) で実行し、
  解けた数・PAR-2・合計時間を比較する。

## 進捗ログ

ベンチマーク: SAT Competition 2023 main track のうち、Kissat 4.0.4 が 1〜30 秒で解く 71 問
(`medium`、SAT 37 / UNSAT 34)。タイムアウト 120 秒、32 並列。PAR-2 は未解決を 240 秒として計算。

| 版 | 解けた数 | UNSAT PAR-2 | SAT PAR-2 | 主な追加 |
|---|---|---|---|---|
| Kissat 4.0.4 (既定) | 71/71 | 258 | 385 | — |
| Kissat (`--simplify=false --lucky=false --preprocess=false`) | 43/71 | 5011 | 2440 | — |
| M1/M2 (inprocessing なし) | 40/71 | 5256 | 3188 | CDCL コア + Kissat 探索ヒューリスティクス |
| + BVE / subsumption | 43/71 | 5085 | 2737 | 変数除去、ゲート (AND/等価) |
| + probing | 46/71 | 4978 | 1910 | ELS 置換、failed literal、vivification |
| + factor | 67/71 | 292 | 1919 | bounded variable addition |
| + congruence / walk | 66/71 | 378 | 2018 | 合同閉包、ProbSAT |
| + lucky / reorder / randec | 70/71 | 314 | 1193 | |
| + sweep / vivify 強化 / factor 修正 / warmup | 69/71 | 289 | ~1450 | SAT 側は試行間のばらつきが大きい |

全 364 問 (120 秒) では crabsat 138 問 / Kissat 137 問 (共通 117 問、SAT/UNSAT の不一致なし)。

検証: 毎段階で `scripts/fuzz.py` (ランダム k-SAT、AMO 構造、miter 回路) を各種オプションで
数千件実行し、Kissat との結果一致・`--check` によるモデル検証・drat-trim による証明検証を確認。

### 2026-10-13: ポートフォリオで誤った SAT を返すバグの修正

OTFS で強化した理由節が衝突節を包含するとき、衝突節を削除していたが、衝突節が既約節で
理由節が冗長節の場合に既約節が失われていた (Kissat は理由節を既約節に昇格させる)。
その後の BVE の復元が失われた節に依存し、不正なモデルが生じた。単独実行でも起こり得るが、
unit 共有で探索経路が変わると頻発した。取り込み unit の記録と再生 (`CRABSAT_IMPORT_LOG` /
`CRABSAT_REPLAY`) と節の追跡 (`CRABSAT_TRACE`) で特定。

| 版 | 解けた数 | UNSAT PAR-2 | SAT PAR-2 |
|---|---|---|---|
| 修正後 単独 | 65/71 | 407 | 2543 |
| 修正後 8 スレッド | 70/71 | 338 | 958 |

(UNSAT 34 問で XOR ゲートを外すと PAR-2 391 → 297 のため、BVE の XOR ゲートは既定で無効化)

### 2026-10-13: Kissat と同等以上に

評価方法を変更: 全 364 問のうち crabsat (旧版/新版) または Kissat が 120 秒以内に解いた
162 問を「union」セットとし、制限 60 秒で Kissat と **同時に同じ負荷で** 実行して比較する
(SAT は試行ごとのばらつきが大きく、別々の時刻の計測は比較できないため)。

主な改善:
- congruence 前の 2リテラル節抽出 (3リテラル節 + 2リテラル節 → 2リテラル節)
- congruence の unit 検出: `(l | o)` と `(l | !o)` から `l` (factor 後の大規模問題で効果大)
- compact (変数の詰め直し、外部/内部番号の分離)
- 簡約処理の遅延 (congruence / sweep / 既約節 vivify)、factor の最小削減量 3
- congruence の高速化 (FxHash、ITE 正規化、XOR のソートによるグループ化)

| union 162 問 / 60 秒 | 解けた数 | SAT | UNSAT | PAR-2 |
|---|---|---|---|---|
| crabsat (1 回目) | 94 | 46 | 48 | 9404 |
| Kissat 4.0.4 (1 回目) | 91 | 48 | 43 | 9775 |
| crabsat (2 回目) | 93 | 45 | 48 | 9477 |
| Kissat 4.0.4 (2 回目) | 93 | 48 | 45 | 9625 |

UNSAT では上回り、SAT ではまだ 2〜3 問少ない。
