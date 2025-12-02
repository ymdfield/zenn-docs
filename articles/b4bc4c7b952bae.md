---
title: "Tagless finalと自由モナド (Freer) の関係"
emoji: "📜"
type: "tech" # tech: 技術記事 / idea: アイデア
topics:
    - "monad"
    - "effect"
    - "TaglessFinal"
published: true
---

# はじめに

本記事は、エフェクトの観点から、Tagless finalと自由モナドの理論上の厳密な等価性と、実際のところの微妙な性質の違いについて示すものです。理解のためには、エフェクトシステムの知識をある程度前提としています。
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
そして、これが`id`となることは2つの型についての任意の値を考えて実際に等式変形すれば証明できますが、イメージを掴むためには、`writeStdout`, `writeStderr`, `readLineStdin`の各場合についての部分関数を考えるとよいでしょう。

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

[^2]: [Capability is about free monads. It's a bird… It's a plane… It's a free monad! 20 March 2019 — by Arnaud Spiwack](https://www.tweag.io/blog/2019-03-20-capability-free-monad/)
[^3]: [Freer Monads: Too Fast, Too Free February 18, 2019 freer-monads, extensible-effects, performance, technical](https://reasonablypolymorphic.com/blog/too-fast-too-free/index.html)
[^4]: 複数の可能な定義（エンコーディング）がありますが、それらは全て等価（同型）です: [Initial and final encodings of free monads Posted on October 20, 2021 - Lysxia](https://blog.poisson.chat/posts/2021-10-20-initial-final-free-monad.html)

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

前節までで、Tagless finalのプログラム

```hs
prog  :: ∀m. C m => m A
```

と、対応する自由モナド版のプログラム

```hs
prog' :: Freer C' A
```

が型としては同型であることを見ました。ここから先は、その同型な二つの表現が、実際の使い方の違いによりどのように性質が分かれるかを見てみます。

## 自由モナドにおける「後からの書き換え」

自由モナドでは、エフェクトの変換関数

```hs
phi :: ∀x. f x -> g x
```

を使って、プログラム内のエフェクトを一括で差し替えるプログラム変換関数

```hs
rewrite :: (∀x. f x -> g x) -> Freer f a -> Freer g a
rewrite phi (Freer k) = Freer $ \h -> k (h . phi)
```

を定義できます。

* `k` は「`f` エフェクトを解釈する関数（エフェクトハンドラ）を渡すとプログラムを実行してくれる関数」
* `h` は「`g` エフェクトのハンドラ」

です。`phi`で`f`を`g`に写し、その先を`h`で解釈することで、`f`で書かれたプログラムを`g`の言葉に翻訳できるわけです。

標準入出力の GADT `Console'` に対しては、例えば標準出力を標準エラーにリダイレクトする関数を

```hs
redirectStderr :: Freer Console' a -> Freer Console' a
redirectStderr =
    rewrite $ \op -> case op of
        WriteStdout s -> WriteStderr s
        WriteStderr s -> WriteStderr s
        ReadLineStdin -> ReadLineStdin
```

のように書けます。ここで重要なのは、`redirectStderr` は `prog' :: Freer Console' A` というプログラム本体にいっさい手を入れずに、その解釈だけを「後から」書き換えている点です。

他にも、自由モナドの方法では、例えば次のようなプログラム変換も比較的容易に行えます。

* 標準出力をそのまま出すと同時にログファイルにも書き出す
* 特定のプレフィックスを持つメッセージだけ無視する
* エラー出力の回数を数えるカウンタを差し込む

いずれも`prog'`の本体の定義には触らずとも外側から可能です。Freerではエフェクトの定義をGADT `Console'` としてデータ化しているため、それを後から好きなように変形しやすい、ということです。

さらに、Tagless finalとの違いとして、例えば同じフックを`n`回適用するようなことが関数合成を使って比較的容易に可能です。
例えば、`!`を出力の末尾に付けるフックを`n`回適用するような処理は次のように書けます:

```hs
emphasizeN :: Int -> Freer Console' a -> Freer Console' a 
emphasizeN 0 = id
emphasizeN n = emphasize . emphasizeN (n-1)

emphasize :: Freer Console' a -> Freer Console' a
emphasize =
    rewrite $ \op -> case op of
        WriteStdout s -> WriteStdout (s ++ "!")
        WriteStderr s -> WriteStderr s
        ReadLineStdin -> ReadLineStdin
```

`n`は実行時にユーザ入力から決めることができます。`Freer`の内部に隠れている`∀m`の量化のおかげで、解釈を与えるタイミング自体を実行時まで遅延させられるので、この種の「動的な書き換え」が自然に書けます。
これがTagless finalではどう難しいかは後ほど述べます。

## Tagless finalで同じことをしようとするとどこで行き詰まる？

自由モナドの`rewrite`に対応するものをTagless finalで書きたい、と考えると、理論的には次のような型が対応することになるでしょう。

```hs
rewriteTF :: ??? -> (∀m. C m => m a) -> (∀m. D m => m a)
```

ここで`C`と`D`はTagless finalで表現したエフェクトの型クラスです。Freer側での`phi :: ∀x. f x -> g x`に対応するものとして、「`C` のエフェクトを `D` のエフェクトに写す何か」を `???` に書きたいのですが、ここで手が止まります。

なぜなら`C` や `D` は普通のデータ型ではなく型クラスだからです。`Console'` のようなGADTであれば「コンストラクタごとの対応」をパターンマッチで列挙してやればよかったのに対し、`C`から`D`への対応を書き下す方法は明らかではありません。Tagless finalでは、`C m` や `D m` は暗黙に渡されている辞書であって、それらをまとめて変形する操作を一つのファーストクラスな値として扱うのが難しいのです。

さらに、`rewriteTF` の型は引数に

```hs
∀m. C m => m a
```

のように量化子を含んでいるので、Rank 2多相になっています。量化子 `∀m` が外側に露出しているため、これがRank 2多相の形でコードの至るところに出てくると型推論が効きづらくなってくるという実用上の問題も出てきそうです。

このRank 2多相の型推論の問題を解決するためには、`newtype`で包む方法が考えられますが、`Freer`型はまさにそのためのものであるという見方もできます。

```hs
newtype Freer f a = Freer (∀m. Monad m => (∀x. f x -> m x) -> m a)
```

つまり、Tagless finalで書かれた「任意の`m`について成立するプログラム」の型を`newtype`でくるむことで表に出る型をRank 1に落としたものが`Freer`と見なせます。言い換えると、`Freer`は「Tagless finalのRank 2多相をうまく隠蔽するためのパッケージ」としても捉えられるということです。

## Tagless finalでの代わりの方法

では、Tagless finalでは自由モナドの`rewrite`のようなことをできないかというとそうではなく、代わりに「専用のキャリアを用意する」方法が典型的に取られます。

先ほどの標準エラーへのリダイレクトであれば、例えば次のようなモナド変換子を導入できます。

```hs
newtype RedirectStderrT m a = RedirectStderrT { runRedirectStderrT :: m a }

instance Console m => Console (RedirectStderrT m) where
    writeStdout s = RedirectStderrT $ writeStderr s
    writeStderr s = RedirectStderrT $ writeStderr s
    readLineStdin = RedirectStderrT readLineStdin
```

`prog :: ∀m. Console m => m A` に対して`runRedirectStderrT`を適用することでモナド変換子を一段積み、標準出力が標準エラーに流れるようにできます。

この方法でも、プログラム本体 `prog` は変更せずに意味だけを書き換えられています。ただし、ここでの違いは「どのキャリアを使うか」をコンパイル時に決めてしまっている点にあります。`RedirectStderrT (LoggingT IO)` のように複数のモナド変換子を積み上げることはできますが、その積み方は型として静的に固定されます。

この制約は、先ほどの「適用回数`n`を実行時に決めるフック」において明らかになります。自由モナドの場合は

```hs
emphasizeN :: Int -> Freer Console' a -> Freer Console' a
emphasizeN n = ...
```

のように、実行時に渡された`n`に応じてフックの適用回数を変えることができました。一方、Tagless finalでは

```hs
newtype EmphasizeT m a = EmphasizeT { runEmphasizeT :: m a }

instance Console m => Console (EmphasizeT m) where
    writeStdout s = EmphasizeT $ writeStdout (s ++ "!")
    writeStderr s = EmphasizeT $ writeStderr s
    readLineStdin = EmphasizeT readLineStdin
```

のような変換子で表されるフックが用意されていたとき、それを動的な回数`n`だけ繰り返すにはどうすればよいでしょうか？
これをやろうとすると、型としては

```hs
EmphasizeT (EmphasizeT ( ... (EmphasizeT m) ... ))
```

という形で`n`回繰り返す必要が出てきます。ところが、`n`は実行時に決まる値なので、その回数分だけ`EmphasizeT`を積むというのは静的に型が付かないことを意味します。

もちろん、`ReaderT Int`を使うなどすることで動的な回数`!`を出力させるようなフックは問題なく書けますが、あくまでそのような変換子を自分で実装する必要があります。
既に用意されている一般のフック処理について、それを`n`回適用する方法はTagless finalでは明らかではありません。

つまり、Tagless finalでは型クラスを使う都合上、必然的に

* `m`はコンパイル時に「どのキャリアを使うか」が決まる静的な型であり
* その上に積む変換子の構造も静的に決まっている

という設計に誘導されるため、**実行時に決まる条件に応じてエフェクトの解釈そのものを差し替えるようなことは自由モナドほど自由にはやりづらい**という違いが出てきます。

## 両者のスタイルの違いとトレードオフ

まとめると、次のような違いが見えます。

* Freerでは、エフェクトをGADTとして表現することで第一級データとして操作しやすくし、さらに
  `Freer f a = Freer (∀m. Monad m => (∀x. f x -> m x) -> m a)`
  の形で`∀m`の量化を`newtype`の内側に閉じ込めているため、解釈を与えるタイミングを実行時まで遅延させやすい。
  その結果として、`rewrite`のような後からのプログラム書き換え、実行時の値に依存する動的なフック挿入が書きやすい。

* Tagless finalでは`m`をエフェクト付き計算のキャリアとしてあらかじめ静的に決めてしまうスタイルに誘導される。
    その代わり、コンパイラは具体的なキャリア型を見ながら最適化がしやすく、データ構造も静的に決まるため、動的ディスパッチのオーバーヘッドがなく高速に動作する傾向にある。

**型のレベルでは両者は同型ですが、「どちら側で何をやると楽か」という実用上の視点では結構違いがあると言えそうです。**
`Console'`のようにGADTとしてエフェクトをデータ化しておくと、後からの書き換えや変換がやりやすいので`rewrite`的なスタイルが発達し、Tagless finalのように型クラスでエフェクトを捉えると、専用キャリアを設計してコンパイル時に決め打つスタイルが発達する、という形で設計が分かれていくのだと理解することができます。

いずれにせよ、後半で述べた性質の違いはかなり微妙なものだと思います。
原理的に機能に違いがあるわけではなく、あくまで実際にプログラミングで使おうとしたときの簡単さの違いであって、これは言語機能のサポートがどの程度あるかといった外部的・環境的な側面が大きいと言えるでしょう。
