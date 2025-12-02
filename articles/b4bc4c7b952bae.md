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

## プログラムを後から「フック」する

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

標準入出力の GADT `Console'` に対しては、例えば標準出力を標準エラーにリダイレクトするプログラム変換関数を

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

いずれも`prog'`の本体の定義には触らずとも外側から可能です。

Tagless finalでも基本的に同様のことができますが、そのやり方は自由モナドと異なっています。それが性質の違いを生みます。

## キャリアのRank 2多相性について

自由モナドの方法で書かれたプログラム変換関数

```hs
hook' :: Freer C' a -> Freer D' a
```

があるとき、理論的には、Tagless finalにおいてこれに対応するのは以下のような関数です。

```
hook :: (∀m. C m => m a) -> (∀m. D m => m a)
```

しかしながらTagless finalの通常のスタイルでは、プログラム変換（フック）を行う関数をこのような型にすることはありません。なぜでしょうか？

これは推測になってしまいますが、一つ考えられるのはRank 2多相を避けたいという理由です。Rank 2多相とは、関数の引数の型の部分に全称量化子`∀`が出現するような型のことです。
一般に、これがあると型推論がうまく働かない場合があります。また第一に目に見えて型が複雑になり、多くのプログラマにとって理解の難易度が上がります[^10]。

[^10]: ところで、Rank 2多相の型推論の問題を解決するためには、`newtype`で包む方法が考えられますが、定義を見ると`Freer`型はまさにそのためのものであるという見方もできます。つまり、Tagless finalで書かれた「任意の`m`について成立するプログラム」の型を`newtype`でくるむことで表に出る型をRank 1に落としたものが`Freer`と見なせます。言い換えると、`Freer`は「Tagless finalのRank 2多相をうまく隠蔽するためのパッケージ」としても捉えられるということです。

代わりに、Haskellでは何らかのモナド変換子`HookT`を用いて

```hs
hook :: HookT m a -> m a
```

のような型を持たせることが多いです。例えば先程の`redirectStderr`の例では

```hs
newtype RedirectStderrT m a = RedirectStderrT { runRedirectStderrT :: m a }
  deriving (Functor, Applicative, Monad)

instance Console m => Console (RedirectStderrT m) where
    writeStdout s = RedirectStderrT $ writeStderr s
    writeStderr s = RedirectStderrT $ writeStderr s
    readLineStdin = RedirectStderrT readLineStdin

redirectStderr :: RedirectStderrT m a -> m a
redirectStderr = runRedirectStderrT
```

のようにできます。
あるいはScalaでは、`using`を使ってエフェクトハンドラの辞書を書き換える方法が典型的に取られるかもしれません:

```scala
def redirectStderrDict[F[_]](original: Console[F]): Console[F] =
    new Console[F] {
        def writeStdout(s: String): F[Unit] = original.writeStderr(s)
        def writeStderr(s: String): F[Unit] = original.writeStderr(s)
        def readLineStdin: F[String]        = original.readLineStdin
    }

// redirectStderrDict で書き換えた辞書を使って prog を変換（解釈変更）する
def redirectStderr[F[_], A](prog: Console[F] ?=> F[A])(using c: Console[F]): F[A] =
    prog(using redirectStderrDict(c))
```

これは型をHaskellに訳すなら、`Console`の辞書型`Console_dict`を使って

```
redirectStderr :: (Monad m => Console_dict m -> m a) -> (Monad m => Console_dict m -> m a)
```

のように表せます。Haskellでは型クラスの辞書を操作する言語機能に乏しいので、言語ごとでこのようなスタイルの違いが生まれるわけです。

いずれにせよ、Tagless finalでは実際のところ共通して以下のスタイルが取られるといえそうです。

- `m`を細かく量化せず、インターフェース全体で共通のものに揃える
- すべての`m`はコンパイル時に決定 (instantiate) される

一方で自由モナドはこの逆です。`m`が具体的にどのようなモナドの型になるかは未定であり、実行時になるまで決定を遅らせることができます。

ほとんどのケースにおいて、このスタイルの違いが露呈することはありません。特にScalaでは`using`を使って辞書のオブジェクトを操作できるので、ほとんどのケースで動的なエフェクト解釈変更に対応できるでしょう。

しかしながら、このスタイルの違いが、ある特定の状況において性質を分けることになります。

## Tagless finalスタイルで書くことが難しい例

Tagless finalスタイルの「`m`を静的に決定する」というやり方では、`m`を動的にしなければならない状況において困ったことになります。

そのような例として、唐突ですが次のようなものを考えてみましょう:

- `writeStderr`が呼び出された回数を特定のルール `rule :: String -> Bool` でカウントし、スコープの最後に、指定したパスのファイルにその回数を書き込むようなフックがしたい
- このフックを、**実行時にユーザから入力される**ファイルパス及びルールのリスト`pathAndRules :: [(FilePath, String -> Bool)]`を使って、すべてのパスに書き込むようにしたい

なお、ここでは話を簡単にするためファイルへの出力は代わりに標準出力へのログの形にすることにします。

### 自由モナドでの実装

まず、自由モナドの方法ではこれは素直に実装できます。

```hs
countStderr :: FilePath -> (String -> Bool) -> Freer Console' a -> Freer Console' a
countStderr path rule (Freer k) = Freer $ \handle -> do

    -- エラーを StateT Int を使ってカウントする処理を追加する
    let countHandle :: Monad m => Console' x -> StateT Int m x
        countHandle op = case op of
            WriteStdout s -> lift $ handle $ WriteStdout s
            WriteStderr s -> do
                when (rule s) $ modify (+1)
                lift $ handle $ WriteStderr s
            ReadLineStdin -> lift $ handle ReadLineStdin

    -- k を StateT Int m 上で解釈する
    (result, n) <- runStateT (k countHandle) 0

    -- 最後にカウントを出力する
    handle $ WriteStdout $ path ++ ": " ++ show count ++ " errors"

    pure result
```

このフックをリスト全部について掛けるためには、単に`foldr`などを使ってフックを関数合成すればよいです。

```hs
multiCountStderr :: [(FilePath, String -> Bool)] -> Freer Console' a -> Freer Console' a
multiCountStderr pathAndRules prog =
    foldr (uncurry countStderr) prog pathAndRules
```

### Tagless finalでの実装

次に、同じフックをTagless finalで書いてみます。

`writeStderr`の回数を数えるためには状態が必要なので、`StateT`を使ったモナド変換子を定義することが必要になります[^11]。

[^11]: 厳密なツッコミを入れると、`IO`や`ST`に依存することで可変参照をエフェクトとして利用することもでき、するとここでの議論が怪しくなるのですが、ここでの「状態が必要」を例えば「非決定性が必要」などに読み替えて、`LogicT`などの非決定性モナド変換子が必要になるような例などを考えることで同様の議論が可能です（すると結構なコーナーケースになってきますが）。

```hs
newtype CountStderrT m a =
    CountStderrT { runCountStderrT :: ReaderT (String -> Bool) (StateT Int m) a }
  deriving (Functor, Applicative, Monad)

instance Console m => Console (CountStderrT m) where
    writeStdout s =
        CountStderrT $ lift $ lift $ writeStdout s

    writeStderr s =
        CountStderrT $ do
            rule <- ask
            when (rule s) $ modify (+1)
            lift $ lift $ writeStderr s

    readLineStdin =
        CountStderrT $ lift $ lift $ readLineStdin

countStderrT :: Console m => FilePath -> (String -> Bool) -> CountStderrT m a -> m a
countStderrT path rule m = do
    (result, count) <- runStateT (runReaderT (runCountStderrT m) rule) 0
    writeStdout $ path ++ ": " ++ show count ++ " errors"
    pure result
```

まず、このフックを一回掛ける用途では、`countStderrT`をあるパス&ルールについて一回適用すればよく、問題ありません。
問題が顕在化するのは、パス&ルールのリストを実行時に受け取り、その長さに応じてフックを何回も重ねたいとなったときです。

```hs
-- やりたいことのイメージ
multiCountStderrT :: Console m => [(FilePath, String -> Bool)] -> ??? -> m a
multiCountStderrT pathAndRules prog = ???
```

`pathAndRules = [("a.log", ...), ("b.log", ...), ("c.log", ...)]`のときには、「`a.log`用のカウンタフック、`b.log`用のカウンタフック、`c.log`用のカウンタフック」を全て差し込みたい、という状況です。
自由モナドの方では`multiCountStderr`を定義できましたが、Tagless finalではリストの長さ分の個数だけ`CountStderrT`が積まれることになります。

もしコンパイル時に決まる長さであれば、例えば2回であれば型は`CountStderrT (CountStderrT m)`、3回であれば`CountStderrT (CountStderrT (CountStderrT m))`のようになるでしょう。
しかし実行時に長さが与えられる一般のリストについて考えようとすると、長さ`n`に応じて

```hs
CountStderrT (CountStderrT ( ... (CountStderrT m) ... ))
```

のような型が必要になりますが、`n`は実行時にしかわからないので、静的に型が付かなくなってしまうのです。

このようなことをやりたい場合、モナド変換子自体に最初から複数回フックを行うための機能を付ける（つまり、`StateT`の状態として`Int`のリストを持つようにする）といった、場合に応じたアドホックな対処が必要になってしまいます。

つまり、既に用意された何らかのフック（プログラム変換）関数があるとき、それを動的な回数だけ掛ける一般的な方法がTagless finalのスタイルではどうやら存在しないようなのです。

ちなみにScalaの場合、`StateT`を使わずにオブジェクトの可変性を利用してカウントするという方法も取れますが、その場合関数は純粋ではなくなり、前半の理論的な等価性についての議論の射程からは外れることになります。

## まとめ

Tagless finalではRank 2多相性の露出を回避したいという都合からか、`m`はコンパイル時にどのキャリアを使うかが決まる静的な型とするという設計のスタイルに行き着くようです。
これにより、**強い動的性が要求される特定の状況において、プログラム変換を自由モナドほど自由にはやりづらい場合がある**という違いが出てきます。
その代わりコンパイラはデータ構造が静的に決まる具体的なキャリア型を見ることができるので最適化がしやすく、また辞書を操作しない場合は動的ディスパッチのオーバーヘッドがなく高速に動作する傾向にあります。

**型のレベルでは両者は同型ですが、「どちら側で何をやると楽か」という実用上の視点では複雑なケースでは微妙な違いがあると言えそうです。**

いずれにせよ、後半で述べた性質の違いはかなり微妙なものだと思います。
原理的に機能に違いがあるわけではなく、あくまで実際にプログラミングで使おうとしたときの簡単さの違いであって、特にRank 2多相について言語機能のサポートがどの程度あるか（どの程度型推論がいい感じに働くか）といった外部的・環境的な側面が大きいと言えるでしょう。
