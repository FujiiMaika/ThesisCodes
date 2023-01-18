# 修士論文に出てくる OCaml と Agda のソースコード

- interpreter/
  - eval01-a/: 代数的エフェクトハンドラのためのCPSインタプリタ (図3.2)
  - eval01-b/: 代数的エフェクトハンドラのためのCPSインタプリタ (図3.3)
  - h-defunc/: eval01-a と eval01-b のそれぞれの型 h を非関数化したインタプリタ (図3.4)
  
  コンパイルするためには [OCamlMakefile](http://www.ocaml.info/software.html#build_tools) が必要です。
  
  eval*/Makefile に OCamlMakefile のパスを書いてください。 
  そして `make` してください。
  
  インタプリタを実行するには `./interpreter` とし、標準入力から プログラムを入力します。
  
  入力例
  - eval01-a/ `try 10 + call_d(3) with (x; k) -> k (x + 1)`
  - eval01-b/ `tryD 10 + call(3) with (x; k) -> k (x + 1)`
  
  
- test-suite/
  - 0/: $\lambda$計算のプログラム例
  - 1/: eval01-a/ のインタプリタ用のプログラム例
    - ハンドラ `try ... with (x, k) -> ...`
    - オペレーション呼び出し 
      - deep なハンドラ用 `call_d(...)`
      - shallow なハンドラ用 `call_s(...)`
  - 2/: eval01-b/ のインタプリタ用のプログラム例
    - deep なハンドラ `tryD ... with (x, k) -> ...`
    - shallow なハンドラ `tryS ... with (x, k) -> ...`
    - オペレーショ呼び出し `call(...)`
  - check*: チェックシステム
    
  インタプリタを実行する際、プログラムを標準入力せず `test-suite/check ./interpreter n` とするとプログラム例を一気に実行できます。
    
    
- typesystem/
  - algebraic.agda: eval01-a のインタプリタから導出した型システムの証明
  
  
- virtual-machine/

  eval01-a のインタプリタからコンパイラと仮想機械を導くまでのプログラム変換
  
  - eval02/: 継続を非関数化
  - eval03/: 継続をリスト化
  - eval04/: スタックを導入
  - eval05/: 継続を非リスト化
  - eval06/: 継続を関数化
  - eval07/: 値とスタックを結合
  - eval08/: 命令に分解
  - eval09/: 非関数化
  - eval10/: 命令をリスト化
  - eval11/: 呼び出し文脈をリスト化
  - proof/
    - 9-10.ml: eval09 から eval10 の変換に関する手書きの証明
    - 10-11.ml: eval10 から eval11 の変換に関する手書きの証明
