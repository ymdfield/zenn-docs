---
title: "Tagless finalと自由モナドの関係"
emoji: "📜"
type: "tech" # tech: 技術記事 / idea: アイデア
topics:
    - "monad"
    - "effect"
    - "TaglessFinal"
published: true
---

# はじめに

本記事は、エフェクトの観点から、Tagless finalと自由モナドの理論上の厳密な等価性と、文化的・スタイル上の微妙な性質の違いについて示すものです。
なおコードにはHaskellを使用します。`forall`は代わりに`∀`と表記します。読者は適宜Scalaなどの他言語に読み替えてください（LLMを使用するとよいかもしれません）。
ここでは、Tagless finalで扱うエフェクトの範囲は一階のもの[^1]に限り、またTagless finalを表現する型クラスのスーパークラスはMonadであることを前提とします（Monadicなエフェクト）。

[^1]: エフェクトの引数として処理ブロック (`do ...`) を取らない、つまり引数の型の部分にモナド`m`が現れないということです。一階でないエフェクトには例えば例外エフェクトの`catch`や`Reader`エフェクトの`local`などがあります。

# Tagless finalと自由モナドの理論的な等価性

Tagless finalでは、例えば標準入出力を扱うエフェクト`Console`を、以下のような型クラスで表現します。

```hs
class Monad m => Console m where
    writeStdout :: String -> m ()
    writeStderr :: String -> m ()
    readLineStdin :: m String
```

そして、`Console`エフェクトを含むようなエフェクト付きプログラム`prog`には以下のような型が付きます。

```hs
prog :: ∀m. Console m => m A
```

一方、自由モナド (`Freer`) の方法では、以下のようなGADTによりエフェクトを表現します。

```hs
data Console' a where
    WriteStdout :: String -> Console' ()
    WriteStderr :: String -> Console' ()
    ReadLineStdin :: Console' String
```

そして、エフェクト付きプログラム`prog'`には以下のような型が付きます。

```hs
prog' :: Freer Console' A
```

一般に、Tagless finalで表現された型クラス `C` と、自由モナドの方法で表現された GADT `C'` は、例から察されるようにある機械的なルールに基づいて相互に変換が可能です。
型クラスの各メソッドをそれぞれGADTのコンストラクタとし、`m`部分をGADTの名前に置き換えればよいです。逆も同様です。
このルールに基づき相互に変換したとき、**Tagless finalにおけるエフェクト付きプログラムの型`∀m. C m => m A`と`Freer C' A`は実は等価（同型）となります**。

## なぜか

`Console`を例にしつつ、同型であることを等価変形により示していきます。
証明に興味がない場合、「まとめ」の所まで読み飛ばして大丈夫です。

まず、`m`を含んでいる任意の型`T(m)`について、`C m => T(m)`という形の型は、辞書型`C_dict`を用いて`Monad m => C_dict m -> T(m)`と同型に変形できます[^5]。
ここで辞書型というのは、各メソッドをそのままメンバとして持つようなレコード型です。`Console`に対しては

[^5]: 本当は辞書型と言うとスーパークラス (`Monad m`) の辞書も`C_dict`のフィールドとして含んでいるべきなのですが、ここでは議論を簡単にするために除いています。

```hs
data Console_dict m = Console_dict
    { writeStdout_dict :: String -> m ()
    , writeStderr_dict :: String -> m ()
    , readLineStdin_dict :: m String
    }
```

が`Console`の辞書型になります。型クラス制約`=>`とは本質的には、型クラスを辞書型と見なした時、暗黙のパラメータとしてその辞書を渡すような仕組みというわけです（これはScalaのimplicitのほうが分かりやすいと思います）。
そして、実はこの辞書型はGADT `Console'` を使うと、以下のように変形できます。

```hs
Console_dict m ≅ (∀x. Console' x -> m x)
```

同型であることを示すには、互いに写しあう関数が存在し、写した後戻したら同じになる（`to`と`from`の合成および`from`と`to`の合成が`id`となる）ことを示せばよいのでした。

```hs
to :: Console_dict m -> (∀x. Console' x -> m x)
to dict = \op -> case op of
    WriteStdout s   -> writeStdout_dict dict s
    WriteStderr s   -> writeStderr_dict dict s
    ReadLineStdin   -> readLineStdin_dict dict

from :: (∀x. Console' x -> m x) -> Console_dict m
from h = Console_dict
    { writeStdout_dict   = \s -> h (WriteStdout s)
    , writeStderr_dict   = \s -> h (WriteStderr s)
    , readLineStdin_dict = h ReadLineStdin
    }
```

これは型チェックが通るので、まずこのような関数のペア`to`/`from`が実際に存在することがわかります。
そして、これが`id`となることは2つの型についての任意の値を考えて実際に等式変形すれば証明できますが、
イメージを掴むためには、`writeStdout`, `writeStderr`, `readLineStdin`の各場合についての部分関数を考えるとよいでしょう。

例えば`writeStdout`に着目すると、ある任意の処理`M(s)`があったとき、

```hs
to $ from $ \(WriteStdout s) -> M(s)
  = to $ Console_dict { writeStdout_dict = \s -> M(s) }
  = \(WriteStdout s) -> M(s)
```

```hs
from $ to $ Console_dict { writeStdout_dict = \s -> M(s) }
  = from $ \(WriteStdout s) -> M(s)
  = Console_dict { writeStdout_dict = \s -> M(s) }
```

のように、きちんと元通りになっています。

## まとめ

まとめると、

```hs
(∀m. Console m => m A)
  ≅ ∀m. Monad m => Console_dict m -> m A
  ≅ ∀m. Monad m => (∀x. Console' x -> m x) -> m A
```

ということです。ここでの `Console`/`Console'` の例は一般の場合 `C`/`C'` でも同じ方法で証明ができます。

そして、実は自由モナド`Freer`は以下で定義できます[^2][^3][^4]。

```hs
data Freer f a = Freer (∀m. Monad m => (∀x. f x -> m x) -> m a)
```

したがって、結局

```hs
(∀m. C m => m A)
  ≅ ∀m. Monad m => (∀x. C' x -> m x) -> m A
  ≅ Freer C' A
```

であり、つまり **Tagless finalで書かれたエフェクト付きプログラムと自由モナドの方法で書かれたエフェクト付きプログラムは、型クラスとGADTの間の対応関係によって理論的に等価** ということです[^6]。

[^6]: 厳密には、ここでの議論における `Freer` のエンコーディング間の同型性はparametricityと呼ばれる性質に依存しています。これはHaskellでは基本的に成り立ちますが、Scalaなど通常の言語では`isinstanceof`などの「量化された型についての型情報を見る」操作により破れ、ここでの議論が成り立たない場合があります。逆に言えば、そのような操作を使わなければ議論に影響はありません。

# 微妙な性質の違い

執筆中です…

[^2]: [Capability is about free monads. It's a bird… It's a plane… It's a free monad! 20 March 2019 — by Arnaud Spiwack](https://www.tweag.io/blog/2019-03-20-capability-free-monad/)
[^3]: [Freer Monads: Too Fast, Too Free February 18, 2019 freer-monads, extensible-effects, performance, technical](https://reasonablypolymorphic.com/blog/too-fast-too-free/index.html)
[^4]: 複数の可能な定義（エンコーディング）がありますが、それらは全て等価（同型）です: [Initial and final encodings of free monads Posted on October 20, 2021 - Lysxia](https://blog.poisson.chat/posts/2021-10-20-initial-final-free-monad.html)
