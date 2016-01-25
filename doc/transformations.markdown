
There are two transformers: The "flatMapper" and the "normalizer". The normalizer
puts trees into normal form so the flatMapper can deal with them. The flatMapper
rewrites trees in mormal form into trees where calls to `value` have been replace
with flatMaps. Normal form means a sequence of statements which can be one of:
  * `$x` where $x does not contain any calls to `value`
  * `value($x)` where x is a stable indentifier
  * `val $var = value($x)` where x is stable
  * `var $var = value($x)` where x is stable

The normalizer has the following set of tricks in its bag
for manipulating the body of a context of type T[U] (invoked
under the given conditions):
  * Split `$a.$b`
    into `val tmp = $a; tmp.b`
    - `$a` contains calls to `value`
  * Turn `value($a)`
    into `val tmp = $a; value(tmp)`
    - `$a` is not stable
  * Turn `$a($arg)`
    into `val tmp = $arg; $a($arg)`
    - `$arg` contains a call to `value`
    - The corresponding parameter is not deferred
  * Turn `$a($arg)`
    into `val tmp = $arg; $a($arg)`
    - `$arg` contains a call to `value`
    - The corresponding parameter is not deferred
  * Turn `if ($cond) $ifTrue else $ifFalse`
    into `val tmp = $cond; if (tmp) $ifTrue else $ifFalse`
    - `$cond` contains a call to `value`
  * Turn `$a || $b`
    into `if ($a) true else $b`
    - `$a` or `$b` contains a call to `value`
  * Turn `$a && $b`
    into `if ($a) $b else false`
    - `$a` or `$b` contains a call to `value`
  * Turn `!($a)`
    into `val tmp = $a; !$tmp`
    - `$a` contains a call to `value`
  * Turn `if ($cond) value($ifTrue) else $ifFalse`
    into `value(if ($cond) $ifTrue else context[T, U]($ifFalse))`
    - `$ifFalse` doesn't contain a call to `value`
  * Turn `value(if ($cond) $ifTrue else context[T, U]($ifFalse))`
    into `value(if ($cond) $ifTrue else context[T, U]($ifFalse))`
    - `$ifTrue` doesn't contain a call to `value`
  * Turn `$a`
    into `value(context[T]($a))`
    - `$a` contains a call to `value`
  * Turn `while($cond) { $body }`
    into `def tmp: T[Unit] = context { if ($cond) { $body; value(tmp) } else () }; value(tmp)`
    - `$cond` or `$body`contains calls to `value`
  * Turn `$x.map($y => $z): $tpe[$elem]`
    into `value($x.foldRight(T($tpe.empty[$elem])) { (a, b) => context[T, $tpe[$elem]] { { val $y = $a; $z } +: value(b) } } )`
    - `$z` contains calls to `value`
  * Turn `$x.flatMap($y => $z): $tpe[$elem]`
    into
    ```
      value($x.foldRight(T($tpe.empty[$elem])) { (a, b) =>
        context[T, $tpe[$elem]] { { val $y = $a; $z } +: value(b) }
      }.map(_.flatten))
    ```
    - `$z` contains calls to `value`
  * Turn `$x.foreach($y => $z): $tpe[$elem]`
    into
    ```
      value($x.foldRight(T($tpe.empty[$elem])) { (a, b) =>
        context[T, $tpe[$elem]] { { val $y = $a; $z } +: value(b) }
      }.map(_ => ()))
    ```
    - `$z` contains calls to `value`
  * Turn `$x.withFilter($y => $z): $tpe[$elem]`
    into
    ```
      value($x.foldRight(T($tpe.empty[$elem])) { (a, b) =>
        context[T, $tpe[$elem]] { if ({ val $y = $a; $z }) a +: value(b) else value(b) }
      })
    ```
    - `$z` contains calls to `value`
