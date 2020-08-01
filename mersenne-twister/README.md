# Formalization of Mersenne-Twister

# How to try it
```
cd /path/to/codegen-examples/mersenne-twister
docker build . -t mt19937
docker run mt19937
```

# Outline for the proof of the long-period (cycle) property

Lemma
  mt.vの整数アルゴリズムと, mt_vec, mt_algの漸化式によるワード列の更新が同値であること
  -> gluing.vにより達成

Lemma
  漸化式によるワード列の更新が, 19937次行列(松本1998では"matrix B". ここでもBとする)
  の作用と同じであること
  -> gluing.vにより達成

Lemma
  Bの特性多項式φBがprimitiveであることと,
  non-zero F2-vector (bit sequence) vに対して
  v, vB, vB^2, ...のperiodが2^19937-1であることが
  同値であること
  -> cycle.vにより達成

Definition (naive)
  primitivityの愚直な計算による判定を, coq内で計算できるように実装
  （実用的な時間内に停止すればよいけれどしなければ次を試す）
  -> 不可能とおもわれる...
     そもそも 0 : 'rV['F_2]_32がまともに計算できない...

Definition (inversive-decimation)
  inversive-decimation methodのアルゴリズムをcoq内で実用的な時間内で停止するように実装

Lemma (reflection; naiveが我慢できる時間内に停止するようなら; 大変かも)
  φBがprimitiveであることと,
  naive algorithmがtrueを返すことが
  同値であること

Lemma (reflection; 大変だろう)
  φBがprimitiveであることと,
  inversive-decimation algorithmがtrueを返すことが
  同値であること

Lemma
  temperingがbijectionであること

Lemma
  従って, temperingはperiodに影響を与えないこと
