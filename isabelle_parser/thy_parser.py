from lark import Lark

import logging


logger = logging.getLogger(__name__)


grammar = r"""
%import common.CNAME -> NAME
%import common.INT -> INT
%import common.WS
%ignore WS
%ignore OUTER_COMMENT

QUOTED_STRING: "\"" /[\s\S]*?/ "\""
             | "`" /[\s\S]*?/ "`"

// Tokens for cartouche
CARTOUCHE_OPEN: "\\<open>"
CARTOUCHE_TEXT: /[^\\]+/
CARTOUCHE_CLOSE: "\\<close>"
CARTOUCHE_SYMBOLS: "\<A>"
                 | "\\-"
                 | "\\,"
                 | "\<AA>"
                 | "\<B>"
                 | "\<BB>"
                 | "\<C>"
                 | "\<CC>"
                 | "\<Colon>"
                 | "\<Coprod>"
                 | "\<D>"
                 | "\<DD>"
                 | "\<Delta>"
                 | "\<Down>"
                 | "\<E>"
                 | "\<EE>"
                 | "\<Empt>"
                 | "\<F>"
                 | "\<FF>"
                 | "\<G>"
                 | "\<GG>"
                 | "\<Gamma>"
                 | "\<H>"
                 | "\<HH>"
                 | "\<I>"
                 | "\<II>"
                 | "\<Inter>"
                 | "\<J>"
                 | "\<JJ>"
                 | "\<Join>"
                 | "\<K>"
                 | "\<KK>"
                 | "\<L>"
                 | "\<LL>"
                 | "\<LM>"
                 | "\<Lambda>"
                 | "\<Leftarrow>"
                 | "\<Leftrightarrow>"
                 | "\<Lleftarrow>"
                 | "\<Longleftarrow>"
                 | "\<Longleftrightarrow>"
                 | "\<Longrightarrow>"
                 | "\<M>"
                 | "\<MM>"
                 | "\<Midarrow>"
                 | "\<Msg>"
                 | "\<N>"
                 | "\<NN>"
                 | "\<NoMsg>"
                 | "\<O>"
                 | "\<OO>"
                 | "\<Odot>"
                 | "\<Omega>"
                 | "\<Oplus>"
                 | "\<Or>"
                 | "\<Otimes>"
                 | "\<P>"
                 | "\<PP>"
                 | "\<PR>"
                 | "\<Parallel>"
                 | "\<Phi>"
                 | "\<Pi>"
                 | "\<Prod>"
                 | "\<Psi>"
                 | "\<Q>"
                 | "\<QQ>"
                 | "\<R>"
                 | "\<RM>"
                 | "\<RR>"
                 | "\<Rightarrow>"
                 | "\<Rrightarrow>"
                 | "\<S>"
                 | "\<SS>"
                 | "\<Sigma>"
                 | "\<Sqinter>"
                 | "\<Squnion>"
                 | "\<Sum>"
                 | "\<T>"
                 | "\<TT>"
                 | "\<TTurnstile>"
                 | "\<Theta>"
                 | "\<Turnstile>"
                 | "\<U>"
                 | "\<UU>"
                 | "\<Union>"
                 | "\<Up>"
                 | "\<Updown>"
                 | "\<Uplus>"
                 | "\<Upsilon>"
                 | "\<V>"
                 | "\<VV>"
                 | "\<W>"
                 | "\<WW>"
                 | "\<X>"
                 | "\<XX>"
                 | "\<Xi>"
                 | "\<Y>"
                 | "\<YY>"
                 | "\<Z>"
                 | "\<ZZ>"
                 | "\<Zinj>"
                 | "\<Zpfun>"
                 | "\<Zsemi>"
                 | "\<Zspot>"
                 | "\<^BibTeX>"
                 | "\<^C>"
                 | "\<^C_theory_text>"
                 | "\<^Const>"
                 | "\<^Const_>"
                 | "\<^LaTeX>"
                 | "\<^ML>"
                 | "\<^ML_file>"
                 | "\<^ML_structure>"
                 | "\<^ML_text>"
                 | "\<^ML_type>"
                 | "\<^TeXLive>"
                 | "\<^Type>"
                 | "\<^abbrev>"
                 | "\<^assert>"
                 | "\<^bindex>"
                 | "\<^binding>"
                 | "\<^bitalic>"
                 | "\<^bold>"
                 | "\<^boxed_bash>"
                 | "\<^boxed_latex>"
                 | "\<^boxed_sml>"
                 | "\<^boxed_text>"
                 | "\<^boxed_theory_text>"
                 | "\<^bsub>"
                 | "\<^bsup>"
                 | "\<^bundle>"
                 | "\<^cancel>"
                 | "\<^cell>"
                 | "\<^cite>"
                 | "\<^citep>"
                 | "\<^citet>"
                 | "\<^class>"
                 | "\<^code>"
                 | "\<^col>"
                 | "\<^command_keyword>"
                 | "\<^const>"
                 | "\<^const_name>"
                 | "\<^const_syntax>"
                 | "\<^context>"
                 | "\<^cterm>"
                 | "\<^ctyp>"
                 | "\<^descr>"
                 | "\<^dir>"
                 | "\<^doc_class>"
                 | "\<^dof>"
                 | "\<^eg>"
                 | "\<^eitalic>"
                 | "\<^emph>"
                 | "\<^enum>"
                 | "\<^esub>"
                 | "\<^esup>"
                 | "\<^etc>"
                 | "\<^figure>"
                 | "\<^file>"
                 | "\<^footnote>"
                 | "\<^here>"
                 | "\<^hfill>"
                 | "\<^htriple>"
                 | "\<^htriple_partial>"
                 | "\<^ie>"
                 | "\<^imp>"
                 | "\<^index>"
                 | "\<^infer_instantiate>"
                 | "\<^instantiate>"
                 | "\<^isadof>"
                 | "\<^item>"
                 | "\<^keyword>"
                 | "\<^latex>"
                 | "\<^locale>"
                 | "\<^lstlisting>"
                 | "\<^ltxinline>"
                 | "\<^make_string>"
                 | "\<^marker>"
                 | "\<^master_dir>"
                 | "\<^medskip>"
                 | "\<^method>"
                 | "\<^morph_infer_instantiate>"
                 | "\<^named_theorems>"
                 | "\<^noindent>"
                 | "\<^nolinkurl>"
                 | "\<^path>"
                 | "\<^path_binding>"
                 | "\<^pattern>"
                 | "\<^pdf>"
                 | "\<^print>"
                 | "\<^prop>"
                 | "\<^ps>"
                 | "\<^rail>"
                 | "\<^row>"
                 | "\<^session>"
                 | "\<^simproc>"
                 | "\<^simproc_setup>"
                 | "\<^sub>"
                 | "\<^sup>"
                 | "\<^syntax_const>"
                 | "\<^technical>"
                 | "\<^term>"
                 | "\<^term_>"
                 | "\<^text>"
                 | "\<^theory>"
                 | "\<^theory_context>"
                 | "\<^theory_text>"
                 | "\<^try>"
                 | "\<^typ>"
                 | "\<^type>"
                 | "\<^type_name>"
                 | "\<^undefined>"
                 | "\<^url>"
                 | "\<^value_>"
                 | "\<^verbatim>"
                 | "\<^vs>"
                 | "\<a>"
                 | "\<aA>"
                 | "\<aC>"
                 | "\<aF>"
                 | "\<aPR>"
                 | "\<aa>"
                 | "\<aans>"
                 | "\<abenv>"
                 | "\<abinit>"
                 | "\<accache>"
                 | "\<aclosure>"
                 | "\<acstate>"
                 | "\<acute>"
                 | "\<ad>"
                 | "\<afstate>"
                 | "\<aleph>"
                 | "\<alpha>"
                 | "\<amalg>"
                 | "\<anb>"
                 | "\<and>"
                 | "\<angle>"
                 | "\<approx>"
                 | "\<aproc>"
                 | "\<avenv>"
                 | "\<b>"
                 | "\<bar>"
                 | "\<bb>"
                 | "\<bbbA>"
                 | "\<bbbD>"
                 | "\<bbbI>"
                 | "\<bbbO>"
                 | "\<bbbP>"
                 | "\<beta>"
                 | "\<bind>"
                 | "\<binit>"
                 | "\<bool>"
                 | "\<bottom>"
                 | "\<bowtie>"
                 | "\<box>"
                 | "\<boxplus>"
                 | "\<bsub>"
                 | "\<bullet>"
                 | "\<c>"
                 | "\<cc>"
                 | "\<cdot>"
                 | "\<cdots>"
                 | "\<checkmark>"
                 | "\<chi>"
                 | "\<circ>"
                 | "\<circle>"
                 | "\<clubsuit>"
                 | "\<comment>"
                 | "\<complex>"
                 | "\<cong>"
                 | "\<congruent>"
                 | "\<currency>"
                 | "\<d>"
                 | "\<dagger>"
                 | "\<dd>"
                 | "\<ddagger>"
                 | "\<degree>"
                 | "\<delta>"
                 | "\<diamond>"
                 | "\<diamondop>"
                 | "\<diamondsuit>"
                 | "\<dieresis>"
                 | "\<div>"
                 | "\<doteq>"
                 | "\<dots>"
                 | "\<doublequote>"
                 | "\<down>"
                 | "\<downharpoonleft>"
                 | "\<downharpoonright>"
                 | "\<e>"
                 | "\<ee>"
                 | "\<eight>"
                 | "\<emptyset>"
                 | "\<epsilon>"
                 | "\<equiv>"
                 | "\<esub>"
                 | "\<eta>"
                 | "\<exclamdown>"
                 | "\<exists>"
                 | "\<ff>"
                 | "\<five>"
                 | "\<flat>"
                 | "\<forall>"
                 | "\<four>"
                 | "\<frown>"
                 | "\<g>"
                 | "\<gamma>"
                 | "\<ge>"
                 | "\<gg>"
                 | "\<ggreater>"
                 | "\<greaterapprox>"
                 | "\<greatersim>"
                 | "\<guillemotleft>"
                 | "\<guillemotright>"
                 | "\<heartsuit>"
                 | "\<hh>"
                 | "\<hole>"
                 | "\<hookleftarrow>"
                 | "\<hookrightarrow>"
                 | "\<hungarumlaut>"
                 | "\<hyphen>"
                 | "\<i>"
                 | "\<ii>"
                 | "\<iinter>"
                 | "\<in>"
                 | "\<index>"
                 | "\<infinity>"
                 | "\<int>"
                 | "\<integral>"
                 | "\<inter>"
                 | "\<inverse>"
                 | "\<iota>"
                 | "\<j>"
                 | "\<jj>"
                 | "\<k>"
                 | "\<kappa>"
                 | "\<kk>"
                 | "\<l>"
                 | "\<lambda>"
                 | "\<langle>"
                 | "\<lblot>"
                 | "\<lbrace>"
                 | "\<lbrakk>"
                 | "\<lceil>"
                 | "\<le>"
                 | "\<leadsto>"
                 | "\<leftarrow>"
                 | "\<leftharpoondown>"
                 | "\<leftharpoonup>"
                 | "\<leftrightarrow>"
                 | "\<lessapprox>"
                 | "\<lesssim>"
                 | "\<lfloor>"
                 | "\<lhd>"
                 | "\<ll>"
                 | "\<llangle>"
                 | "\<lless>"
                 | "\<longleftarrow>"
                 | "\<longleftrightarrow>"
                 | "\<longlonglongrightarrow>"
                 | "\<longlongrightarrow>"
                 | "\<longmapsto>"
                 | "\<longrightarrow>"
                 | "\<lozenge>"
                 | "\<lparr>"
                 | "\<m>"
                 | "\<mapsto>"
                 | "\<mho>"
                 | "\<midarrow>"
                 | "\<minusplus>"
                 | "\<mm>"
                 | "\<mu>"
                 | "\<nabla>"
                 | "\<nat>"
                 | "\<natural>"
                 | "\<newline>"
                 | "\<nexists>"
                 | "\<nine>"
                 | "\<nn>"
                 | "\<not>"
                 | "\<notTurnstile>"
                 | "\<noteq>"
                 | "\<notin>"
                 | "\<notsqsubseteq>"
                 | "\<notturnstile>"
                 | "\<nu>"
                 | "\<o>"
                 | "\<odot>"
                 | "\<ointegral>"
                 | "\<omega>"
                 | "\<ominus>"
                 | "\<one>"
                 | "\<onehalf>"
                 | "\<oo>"
                 | "\<oplus>"
                 | "\<or>"
                 | "\<oslash>"
                 | "\<otimes>"
                 | "\<p>"
                 | "\<paragraph>"
                 | "\<parallel>"
                 | "\<partial>"
                 | "\<phi>"
                 | "\<pi>"
                 | "\<plusminus>"
                 | "\<pp>"
                 | "\<prec>"
                 | "\<preceq>"
                 | "\<propto>"
                 | "\<psi>"
                 | "\<q>"
                 | "\<qq>"
                 | "\<questiondown>"
                 | "\<quote>"
                 | "\<r>"
                 | "\<rangle>"
                 | "\<rat>"
                 | "\<rblot>"
                 | "\<rbrace>"
                 | "\<rbrakk>"
                 | "\<rceil>"
                 | "\<real>"
                 | "\<registered>"
                 | "\<restriction>"
                 | "\<rfloor>"
                 | "\<rhd>"
                 | "\<rho>"
                 | "\<rightarrow>"
                 | "\<rightharpoondown>"
                 | "\<rightharpoonup>"
                 | "\<rightleftharpoons>"
                 | "\<rparr>"
                 | "\<rr>"
                 | "\<rrangle>"
                 | "\<s>"
                 | "\<section>"
                 | "\<setminus>"
                 | "\<seven>"
                 | "\<sharp>"
                 | "\<sigma>"
                 | "\<sim>"
                 | "\<simeq>"
                 | "\<six>"
                 | "\<smile>"
                 | "\<some>"
                 | "\<spadesuit>"
                 | "\<sqdot>"
                 | "\<sqinter>"
                 | "\<sqrt>"
                 | "\<sqsubset>"
                 | "\<sqsubseteq>"
                 | "\<sqsupset>"
                 | "\<sqsupseteq>"
                 | "\<squnion>"
                 | "\<ss>"
                 | "\<sslash>"
                 | "\<star>"
                 | "\<stileturn>"
                 | "\<sub>"
                 | "\<subset>"
                 | "\<subseteq>"
                 | "\<succ>"
                 | "\<succeq>"
                 | "\<supset>"
                 | "\<supseteq>"
                 | "\<surd>"
                 | "\<t>"
                 | "\<tau>"
                 | "\<then>"
                 | "\<theta>"
                 | "\<three>"
                 | "\<times>"
                 | "\<top>"
                 | "\<triangle>"
                 | "\<triangleleft>"
                 | "\<triangleq>"
                 | "\<triangleright>"
                 | "\<tt>"
                 | "\<tturnstile>"
                 | "\<turnstile>"
                 | "\<two>"
                 | "\<union>"
                 | "\<unlhd>"
                 | "\<unrhd>"
                 | "\<up>"
                 | "\<updown>"
                 | "\<upharpoonleft>"
                 | "\<uplus>"
                 | "\<upsilon>"
                 | "\<v>"
                 | "\<vv>"
                 | "\<w>"
                 | "\<wrong>"
                 | "\<ww>"
                 | "\<xi>"
                 | "\<xx>"
                 | "\<yy>"
                 | "\<zero>"
                 | "\<zeta>"
                 | "\<zz>"
                 | "\\ "
                 | "\\#"
                 | "\\<And>"
                 | "\\<D>"
                 | "\\<F>"
                 | "\\<K>"
                 | "\\<Longrightarrow>"
                 | "\\<R>"
                 | "\\<Rightarrow>"
                 | "\\<Sqinter>"
                 | "\\<Sum>"
                 | "\\<T>"
                 | "\\<TTurnstile>"
                 | "\\<Turnstile>"
                 | "\\<Union>"
                 | "\\<W>"
                 | "\\<^bold>"
                 | "\\<^bsub>"
                 | "\\<^cite>"
                 | "\\<^const>"
                 | "\\<^descr>"
                 | "\\<^enum>"
                 | "\\<^esub>"
                 | "\\<^item>"
                 | "\\<^locale>"
                 | "\\<^noindent>"
                 | "\\<^sub>"
                 | "\\<^sup>"
                 | "\\<^term>"
                 | "\\<^typ>"
                 | "\\<and>"
                 | "\\<bottom>"
                 | "\\<box>"
                 | "\\<checkmark>"
                 | "\\<equiv>"
                 | "\\<exists>"
                 | "\\<for>"
                 | "\\<forall>"
                 | "\\<ge>"
                 | "\\<guillemotleft>"
                 | "\\<guillemotright>"
                 | "\\<in>"
                 | "\\<integral>"
                 | "\\<inter>"
                 | "\\<lambda>"
                 | "\\<lbrakk>"
                 | "\\<le>"
                 | "\\<leadsto>"
                 | "\\<longleftrightarrow>"
                 | "\\<longmapsto>"
                 | "\\<longrightarrow>"
                 | "\\<lparr>"
                 | "\\<midarrow>"
                 | "\\<not>"
                 | "\\<noteq>"
                 | "\\<notin>"
                 | "\\<oplus>"
                 | "\\<or>"
                 | "\\<otimes>"
                 | "\\<rbrakk>"
                 | "\\<rhd>"
                 | "\\<rightarrow>"
                 | "\\<rparr>"
                 | "\\<sqinter>"
                 | "\\<sqsubseteq>"
                 | "\\<star>"
                 | "\\<subseteq>"
                 | "\\<surd>"
                 | "\\<turnstile>"
                 | "\\<union>"
                 | "\\A"
                 | "\\AA"
                 | "\\AC"
                 | "\\ActSemimodule"
                 | "\\Agent"
                 | "\\An"
                 | "\\As"
                 | "\\AtBeginDocument"
                 | "\\BNFCC"
                 | "\\BNFCC"
                 | "\\BODY"
                 | "\\Because"
                 | "\\BibTeX"
                 | "\\Box"
                 | "\\C"
                 | "\\CCKAabbrv"
                 | "\\CH"
                 | "\\CKAabbrv"
                 | "\\CKAenc"
                 | "\\CKAencompass"
                 | "\\CKAiterPar"
                 | "\\CKAiterSeq"
                 | "\\CKAle"
                 | "\\CKApar"
                 | "\\CKAseq"
                 | "\\CKAset"
                 | "\\CKAsim"
                 | "\\CKAstructure"
                 | "\\Coloneqq"
                 | "\\CryptHOL"
                 | "\\DOFauthor"
                 | "\\DTcomment"
                 | "\\Def"
                 | "\\DefineSnippet"
                 | "\\Delta"
                 | "\\Diamond"
                 | "\\Dstim"
                 | "\\E"
                 | "\\ENVcomm"
                 | "\\ENVcommD"
                 | "\\Even"
                 | "\\Ex"
                 | "\\FOCL"
                 | "\\Finally"
                 | "\\First"
                 | "\\FloatBarrier"
                 | "\\Gamma"
                 | "\\H"
                 | "\\HOL"
                 | "\\HolOclOidOf"
                 | "\\However"
                 | "\\If"
                 | "\\IfFileExists"
                 | "\\In"
                 | "\\Indeed"
                 | "\\L"
                 | "\\LE"
                 | "\\LaTeX"
                 | "\\LaTeXë"
                 | "\\Lambda"
                 | "\\Large"
                 | "\\Leftrightarrow"
                 | "\\Longleftrightarrow"
                 | "\\Longrightarrow"
                 | "\\N"
                 | "\\NE"
                 | "\\NN"
                 | "\\NP"
                 | "\\Nat"
                 | "\\NewEnviron"
                 | "\\Next"
                 | "\\Nstim"
                 | "\\OCL"
                 | "\\Observe"
                 | "\\Odd"
                 | "\\Omega"
                 | "\\Ors"
                 | "\\Otherwise"
                 | "\\OutSemimodule"
                 | "\\P"
                 | "\\PackageError"
                 | "\\Phi"
                 | "\\Pi"
                 | "\\Pr"
                 | "\\Psi"
                 | "\\RR"
                 | "\\Re"
                 | "\\Rightarrow"
                 | "\\S"
                 | "\\SAT"
                 | "\\SC"
                 | "\\SLE"
                 | "\\SN"
                 | "\\STIMbasic"
                 | "\\STIMcomm"
                 | "\\STIMcommD"
                 | "\\STIMcommN"
                 | "\\STIMdot"
                 | "\\STIMenc"
                 | "\\STIMle"
                 | "\\STIMplus"
                 | "\\STIMset"
                 | "\\STIMstructure"
                 | "\\STbot"
                 | "\\STdiff"
                 | "\\STleq"
                 | "\\Sigma"
                 | "\\Since"
                 | "\\Such"
                 | "\\TTurnstile"
                 | "\\TeX"
                 | "\\TeXLive"
                 | "\\The"
                 | "\\Then"
                 | "\\These"
                 | "\\Theta"
                 | "\\This"
                 | "\\Thus"
                 | "\\To"
                 | "\\Upsilon"
                 | "\\Var"
                 | "\\Vert"
                 | "\\ZF"
                 | "\\ZFC"
                 | "\\\""
                 | "\\_"
                 | "\\a"
                 | "\\actOp"
                 | "\\addaffiliation"
                 | "\\addauthor"
                 | "\\addcontentsline"
                 | "\\addplot"
                 | "\\addtolength"
                 | "\\agent"
                 | "\\aleph"
                 | "\\all"
                 | "\\alpah"
                 | "\\alpha"
                 | "\\and"
                 | "\\ap"
                 | "\\append"
                 | "\\approx"
                 | "\\ar"
                 | "\\arccos"
                 | "\\arcsin"
                 | "\\arraycolsep"
                 | "\\arrow"
                 | "\\ast"
                 | "\\asymp"
                 | "\\ate"
                 | "\\author"
                 | "\\autoref"
                 | "\\b"
                 | "\\bar"
                 | "\\baseheight"
                 | "\\baselineskip"
                 | "\\basewidth"
                 | "\\bbOI"
                 | "\\bbbI"
                 | "\\bbbO"
                 | "\\bcancel"
                 | "\\begin"
                 | "\\begin"
                 | "\\begingroup"
                 | "\\beta"
                 | "\\bf"
                 | "\\bfseries"
                 | "\\bibliography"
                 | "\\big"
                 | "\\bigA"
                 | "\\bigbreak"
                 | "\\bigcap"
                 | "\\bigcup"
                 | "\\bigg"
                 | "\\biggl"
                 | "\\biggr"
                 | "\\bigl"
                 | "\\biglnotation"
                 | "\\bigotimes"
                 | "\\bigr"
                 | "\\bigskip"
                 | "\\bigskip"
                 | "\\bigsqcup"
                 | "\\bigvee"
                 | "\\bigwedge"
                 | "\\biimp"
                 | "\\bindex"
                 | "\\binom"
                 | "\\blackdot"
                 | "\\bluecircle"
                 | "\\bluesquare"
                 | "\\bmod"
                 | "\\bot"
                 | "\\bottomrule"
                 | "\\box"
                 | "\\break"
                 | "\\bullet"
                 | "\\c"
                 | "\\cal"
                 | "\\calV"
                 | "\\cap"
                 | "\\caption"
                 | "\\captionsetup"
                 | "\\cdot"
                 | "\\cdot"
                 | "\\cdots"
                 | "\\center"
                 | "\\centering"
                 | "\\ceta"
                 | "\\chapref"
                 | "\\chapter"
                 | "\\chapterauthor"
                 | "\\checkmark"
                 | "\\chi"
                 | "\\choose"
                 | "\\circ"
                 | "\\cite"
                 | "\\citeauthor"
                 | "\\citep"
                 | "\\citet"
                 | "\\cka"
                 | "\\clearpage"
                 | "\\clearpage"
                 | "\\close"
                 | "\\colon"
                 | "\\color"
                 | "\\columnsep"
                 | "\\commandkey"
                 | "\\comment"
                 | "\\cong"
                 | "\\constructor"
                 | "\\coordinate"
                 | "\\coprod"
                 | "\\cormen"
                 | "\\cos"
                 | "\\create"
                 | "\\cref"
                 | "\\csname"
                 | "\\cup"
                 | "\\d"
                 | "\\dagger"
                 | "\\dash"
                 | "\\dashv"
                 | "\\ddltwocell"
                 | "\\ddrtwocell"
                 | "\\ddtwocell"
                 | "\\def"
                 | "\\definecolor"
                 | "\\deg"
                 | "\\delete"
                 | "\\delta"
                 | "\\dep"
                 | "\\depOp"
                 | "\\depOpTC"
                 | "\\depTC"
                 | "\\dfrac"
                 | "\\diamond"
                 | "\\diamondsuit"
                 | "\\dir"
                 | "\\dirtree"
                 | "\\displaystyle"
                 | "\\div"
                 | "\\documentclass"
                 | "\\dof"
                 | "\\dofurl"
                 | "\\dom"
                 | "\\dots"
                 | "\\dotsb"
                 | "\\dotsc"
                 | "\\doublecap"
                 | "\\downarrow"
                 | "\\draw"
                 | "\\drop"
                 | "\\drtwocell"
                 | "\\dtwocell"
                 | "\\e"
                 | "\\eg"
                 | "\\eigbyz"
                 | "\\ell"
                 | "\\em"
                 | "\\email"
                 | "\\embeddedstyle"
                 | "\\emph"
                 | "\\emph"
                 | "\\emptyset"
                 | "\\end"
                 | "\\end"
                 | "\\endcsname"
                 | "\\endgroup"
                 | "\\endisaantiq"
                 | "\\endisatagafp"
                 | "\\endisatagannexa"
                 | "\\endxy"
                 | "\\enskip"
                 | "\\enspace"
                 | "\\ensuremath"
                 | "\\env"
                 | "\\epigraph"
                 | "\\epsilon"
                 | "\\eq"
                 | "\\eqnum"
                 | "\\eqref"
                 | "\\equal"
                 | "\\equiv"
                 | "\\ess"
                 | "\\eta"
                 | "\\etc"
                 | "\\evalmu"
                 | "\\evalnu"
                 | "\\ex"
                 | "\\exists"
                 | "\\exp"
                 | "\\expandafter"
                 | "\\expunge"
                 | "\\extrah"
                 | "\\f"
                 | "\\fbox"
                 | "\\file"
                 | "\\filldraw"
                 | "\\flatten"
                 | "\\flattentwo"
                 | "\\footnote"
                 | "\\footnote"
                 | "\\footnotesize"
                 | "\\forall"
                 | "\\forces"
                 | "\\frac"
                 | "\\framebox"
                 | "\\from"
                 | "\\fsub"
                 | "\\fundesc"
                 | "\\funheadersep"
                 | "\\fussy"
                 | "\\fw"
                 | "\\gamma"
                 | "\\gausslucasexample"
                 | "\\gcalt"
                 | "\\gcd"
                 | "\\gdef"
                 | "\\ge"
                 | "\\genfrac"
                 | "\\geq"
                 | "\\geqslant"
                 | "\\gg"
                 | "\\h"
                 | "\\hat"
                 | "\\hbox"
                 | "\\hfill"
                 | "\\hline"
                 | "\\holkeyword"
                 | "\\href"
                 | "\\hrulefill"
                 | "\\hskip"
                 | "\\hspace"
                 | "\\ht"
                 | "\\htmllink"
                 | "\\huge"
                 | "\\hyp"
                 | "\\hyperlink"
                 | "\\hypertarget"
                 | "\\i"
                 | "\\ie"
                 | "\\iff"
                 | "\\ifthenelse"
                 | "\\immediate"
                 | "\\imp"
                 | "\\implies"
                 | "\\in"
                 | "\\includegraphics"
                 | "\\indent"
                 | "\\index"
                 | "\\induced"
                 | "\\inf"
                 | "\\infer"
                 | "\\inferrule"
                 | "\\infty"
                 | "\\inline"
                 | "\\inlinebash"
                 | "\\inlineisar"
                 | "\\inlineltx"
                 | "\\inlineocl"
                 | "\\inlinetrac"
                 | "\\input"
                 | "\\inputpos"
                 | "\\inst"
                 | "\\institution"
                 | "\\int"
                 | "\\inv"
                 | "\\iota"
                 | "\\isa"
                 | "\\isaDof"
                 | "\\isaDofDOTlabel"
                 | "\\isaDofDOTmacroDef"
                 | "\\isaDofDOTmacroExp"
                 | "\\isaDofDOTref"
                 | "\\isaantiq"
                 | "\\isacartoucheclose"
                 | "\\isacartoucheopen"
                 | "\\isachapter"
                 | "\\isacharampersand"
                 | "\\isacharbackquoteclose"
                 | "\\isacharbackquoteopen"
                 | "\\isacharbar"
                 | "\\isacharbrackleft"
                 | "\\isacharbrackright"
                 | "\\isacharcolon"
                 | "\\isachardot"
                 | "\\isachardoublequoteclose"
                 | "\\isachardoublequoteopen"
                 | "\\isacharequal"
                 | "\\isacharparenleft"
                 | "\\isacharparenright"
                 | "\\isacharprime"
                 | "\\isacharquery"
                 | "\\isacharsemicolon"
                 | "\\isacharunderscore"
                 | "\\isacommand"
                 | "\\isactrlsub"
                 | "\\isadigit"
                 | "\\isadof"
                 | "\\isafor"
                 | "\\isaheader"
                 | "\\isaheader"
                 | "\\isakeyword"
                 | "\\isamarkupcancel"
                 | "\\isamarkupcmt"
                 | "\\isamarkupfalse"
                 | "\\isamarkupsection"
                 | "\\isamarkuptrue"
                 | "\\isaname"
                 | "\\isanewline"
                 | "\\isasection"
                 | "\\isastyle"
                 | "\\isastyletext"
                 | "\\isasymAnd"
                 | "\\isasymLongrightarrow"
                 | "\\isasymRightarrow"
                 | "\\isasymS"
                 | "\\isasymT"
                 | "\\isasymequiv"
                 | "\\isasymint"
                 | "\\isasymlbrakk"
                 | "\\isasymle"
                 | "\\isasymmapsto"
                 | "\\isasymnoteq"
                 | "\\isasymparallel"
                 | "\\isasymrbrakk"
                 | "\\isasymrhd"
                 | "\\isasymrho"
                 | "\\isasymsigma"
                 | "\\isasymstar"
                 | "\\isasymtau"
                 | "\\isasymupsilon"
                 | "\\isatagafp"
                 | "\\isatagannexa"
                 | "\\isatext"
                 | "\\isb"
                 | "\\it"
                 | "\\item"
                 | "\\item"
                 | "\\jensenexample"
                 | "\\jive"
                 | "\\justif"
                 | "\\kappa"
                 | "\\kern"
                 | "\\knows"
                 | "\\lAct"
                 | "\\lOut"
                 | "\\lSact"
                 | "\\lVert"
                 | "\\labarrow"
                 | "\\label"
                 | "\\label"
                 | "\\lambda"
                 | "\\land"
                 | "\\langle"
                 | "\\large"
                 | "\\lbrace"
                 | "\\lceil"
                 | "\\lcomp"
                 | "\\lcreate"
                 | "\\ldots"
                 | "\\le"
                 | "\\leadsto"
                 | "\\left"
                 | "\\leftAct"
                 | "\\leftSemimodule"
                 | "\\leftadd"
                 | "\\leftaddaux"
                 | "\\leftarrow"
                 | "\\leftmargin"
                 | "\\leq"
                 | "\\leqslant"
                 | "\\let"
                 | "\\lfloor"
                 | "\\lfst"
                 | "\\lg"
                 | "\\lget"
                 | "\\lhd"
                 | "\\lim"
                 | "\\liminf"
                 | "\\limits"
                 | "\\limsup"
                 | "\\linebreak"
                 | "\\linelabel"
                 | "\\linewidth"
                 | "\\llbracket"
                 | "\\ln"
                 | "\\lnot"
                 | "\\lnotation"
                 | "\\log"
                 | "\\longleftrightarrow"
                 | "\\longrightarrow"
                 | "\\lor"
                 | "\\lower"
                 | "\\lowercase"
                 | "\\lput"
                 | "\\lquot"
                 | "\\lsnd"
                 | "\\lstinline"
                 | "\\lstinputlisting"
                 | "\\lt"
                 | "\\ltimes"
                 | "\\lto"
                 | "\\lvert"
                 | "\\maketitle"
                 | "\\mapsto"
                 | "\\mathbb"
                 | "\\mathbf"
                 | "\\mathbin"
                 | "\\mathcal"
                 | "\\mathfrak"
                 | "\\mathit"
                 | "\\mathop"
                 | "\\mathrel"
                 | "\\mathrm"
                 | "\\mathscr"
                 | "\\mathsf"
                 | "\\mathtt"
                 | "\\max"
                 | "\\mbox"
                 | "\\medskip"
                 | "\\mid"
                 | "\\middle"
                 | "\\midrule"
                 | "\\min"
                 | "\\mod"
                 | "\\models"
                 | "\\mu"
                 | "\\multicolumn"
                 | "\\myboxi"
                 | "\\myboxii"
                 | "\\myboxiii"
                 | "\\myboxiv"
                 | "\\mycomment"
                 | "\\mydimeni"
                 | "\\mydimenii"
                 | "\\myscale"
                 | "\\myskip"
                 | "\\myskipamount"
                 | "\\myurl"
                 | "\\n"
                 | "\\nAUhiZshToFJJDerqQwxgQ"
                 | "\\nAnd"
                 | "\\nCNdKebOrUVtPL"
                 | "\\nExpected"
                 | "\\nFbP"
                 | "\\nIn"
                 | "\\nKSdw"
                 | "\\nMCH"
                 | "\\nMIIEpAIBAAKCAQEAwyzQ"
                 | "\\nMaybe"
                 | "\\nOTg"
                 | "\\nOrJNHvAPjSFM"
                 | "\\nOriginal"
                 | "\\nPlease"
                 | "\\nProbable"
                 | "\\nPt"
                 | "\\nS"
                 | "\\nThe"
                 | "\\nValid"
                 | "\\nVmtx"
                 | "\\nWVp"
                 | "\\nX"
                 | "\\nYHq"
                 | "\\nYTgMu"
                 | "\\nYplS"
                 | "\\nabla"
                 | "\\nat"
                 | "\\nats"
                 | "\\nbut"
                 | "\\ncannot"
                 | "\\ne"
                 | "\\neDuZ"
                 | "\\nec"
                 | "\\needleangle"
                 | "\\needlelength"
                 | "\\needlethickness"
                 | "\\neg"
                 | "\\neq"
                 | "\\newcommand"
                 | "\\newcounter"
                 | "\\newisadof"
                 | "\\newkeycommand"
                 | "\\newlength"
                 | "\\newline"
                 | "\\newpage"
                 | "\\nfoo"
                 | "\\nhas"
                 | "\\nicefrac"
                 | "\\nin"
                 | "\\nkVaiMZMvZxslF"
                 | "\\nksmYtg"
                 | "\\nmid"
                 | "\\node"
                 | "\\noexpand"
                 | "\\noindent"
                 | "\\noindent"
                 | "\\nolimits"
                 | "\\nolinkurl"
                 | "\\nondet"
                 | "\\nonumber"
                 | "\\nopagebreak"
                 | "\\normalfont"
                 | "\\normalsize"
                 | "\\not"
                 | "\\notin"
                 | "\\nrMgklhl"
                 | "\\ns"
                 | "\\nsAscPlcZCMm"
                 | "\\nsim"
                 | "\\nsubseteq"
                 | "\\nt"
                 | "\\ntN"
                 | "\\nu"
                 | "\\null"
                 | "\\odot"
                 | "\\oid"
                 | "\\omega"
                 | "\\ominus"
                 | "\\omit"
                 | "\\open"
                 | "\\operatorname"
                 | "\\oplus"
                 | "\\orb"
                 | "\\orbS"
                 | "\\orcidID"
                 | "\\ord"
                 | "\\otimes"
                 | "\\outOp"
                 | "\\over"
                 | "\\overbrace"
                 | "\\overline"
                 | "\\overrightarrow"
                 | "\\overset"
                 | "\\p"
                 | "\\pagebreak"
                 | "\\pageref"
                 | "\\par"
                 | "\\paragraph"
                 | "\\paragraph"
                 | "\\parallel"
                 | "\\parbox"
                 | "\\parencite"
                 | "\\parindent"
                 | "\\part"
                 | "\\partial"
                 | "\\pat"
                 | "\\path"
                 | "\\pf"
                 | "\\phantom"
                 | "\\phi"
                 | "\\pi"
                 | "\\pm"
                 | "\\pmod"
                 | "\\polhk"
                 | "\\pos"
                 | "\\prec"
                 | "\\preceq"
                 | "\\precsim"
                 | "\\prev"
                 | "\\prime"
                 | "\\prod"
                 | "\\prompt"
                 | "\\protect"
                 | "\\protected"
                 | "\\provideisadof"
                 | "\\providekeycommand"
                 | "\\psi"
                 | "\\put"
                 | "\\qed"
                 | "\\qquad"
                 | "\\qt"
                 | "\\quad"
                 | "\\quotient"
                 | "\\r"
                 | "\\rKact"
                 | "\\rVert"
                 | "\\raise"
                 | "\\rangle"
                 | "\\rats"
                 | "\\ratsb"
                 | "\\rbrace"
                 | "\\rceil"
                 | "\\reals"
                 | "\\ref"
                 | "\\ref"
                 | "\\refl"
                 | "\\refsto"
                 | "\\renewcommand"
                 | "\\renewisadof"
                 | "\\renewkeycommand"
                 | "\\resizebox"
                 | "\\rfloor"
                 | "\\rhd"
                 | "\\rho"
                 | "\\right"
                 | "\\rightAct"
                 | "\\rightSemimodule"
                 | "\\rightarrow"
                 | "\\rightarrowtail"
                 | "\\rightharpoonup"
                 | "\\rightsquigarrow"
                 | "\\rm"
                 | "\\rrbracket"
                 | "\\rrtwocell"
                 | "\\rulelen"
                 | "\\rulenamelen"
                 | "\\rvert"
                 | "\\sc"
                 | "\\scalebox"
                 | "\\scriptsize"
                 | "\\scriptstyle"
                 | "\\secref"
                 | "\\secref"
                 | "\\section"
                 | "\\set"
                 | "\\setbox"
                 | "\\setlength"
                 | "\\setminus"
                 | "\\sets"
                 | "\\settoheight"
                 | "\\settowidth"
                 | "\\sf"
                 | "\\sffamily"
                 | "\\sharp"
                 | "\\sigma"
                 | "\\sim"
                 | "\\sin"
                 | "\\sinh"
                 | "\\sl"
                 | "\\sloppy"
                 | "\\sloppypar"
                 | "\\small"
                 | "\\smallskip"
                 | "\\smallskipamount"
                 | "\\smash"
                 | "\\smile"
                 | "\\snip"
                 | "\\snip"
                 | "\\spot"
                 | "\\spray"
                 | "\\sqcap"
                 | "\\sqcup"
                 | "\\sqrt"
                 | "\\sqsubseteq"
                 | "\\sqsupseteq"
                 | "\\src"
                 | "\\ss"
                 | "\\stab"
                 | "\\stackrel"
                 | "\\star"
                 | "\\state"
                 | "\\stepcounter"
                 | "\\stim"
                 | "\\stop"
                 | "\\store"
                 | "\\string"
                 | "\\strut"
                 | "\\subfloat"
                 | "\\subsection"
                 | "\\subset"
                 | "\\subseteq"
                 | "\\substack"
                 | "\\subsubsection"
                 | "\\succ"
                 | "\\succeq"
                 | "\\sum"
                 | "\\sup"
                 | "\\supset"
                 | "\\supseteq"
                 | "\\t"
                 | "\\table"
                 | "\\tabto"
                 | "\\tag"
                 | "\\tan"
                 | "\\tau"
                 | "\\td"
                 | "\\texorpdfstring"
                 | "\\text"
                 | "\\textbf"
                 | "\\textdegree"
                 | "\\textelp"
                 | "\\textheight"
                 | "\\textins"
                 | "\\textit"
                 | "\\textquote"
                 | "\\textrm"
                 | "\\textsc"
                 | "\\textsection"
                 | "\\textsf"
                 | "\\textsl"
                 | "\\textstyle"
                 | "\\textsuperscript"
                 | "\\texttt"
                 | "\\texttt"
                 | "\\textwidth"
                 | "\\tfrac"
                 | "\\tfreeify"
                 | "\\thedof"
                 | "\\theta"
                 | "\\thy"
                 | "\\tikzset"
                 | "\\tikzstyle"
                 | "\\tilde"
                 | "\\times"
                 | "\\times"
                 | "\\tiny"
                 | "\\tlastar"
                 | "\\tnote"
                 | "\\to"
                 | "\\todo"
                 | "\\top"
                 | "\\toprule"
                 | "\\tp"
                 | "\\triangle"
                 | "\\triangleq"
                 | "\\triangleright"
                 | "\\tt"
                 | "\\tv"
                 | "\\twocolumn"
                 | "\\ulcorner"
                 | "\\uline"
                 | "\\underbrace"
                 | "\\underline"
                 | "\\underset"
                 | "\\unlhd"
                 | "\\uparrow"
                 | "\\uplambda"
                 | "\\uplus"
                 | "\\upshape"
                 | "\\upshape"
                 | "\\urcorner"
                 | "\\url"
                 | "\\urtwocell"
                 | "\\usepackage"
                 | "\\ute"
                 | "\\v"
                 | "\\vDash"
                 | "\\var"
                 | "\\varepsilon"
                 | "\\varnothing"
                 | "\\varphi"
                 | "\\vartheta"
                 | "\\vcenter"
                 | "\\vdash"
                 | "\\vdots"
                 | "\\vec"
                 | "\\vee"
                 | "\\verb"
                 | "\\vfill"
                 | "\\view"
                 | "\\voelzer"
                 | "\\vsep"
                 | "\\vskip"
                 | "\\vspace"
                 | "\\vthinspace"
                 | "\\wd"
                 | "\\wedge"
                 | "\\whitedot"
                 | "\\widehat"
                 | "\\write"
                 | "\\www"
                 | "\\x"
                 | "\\xIc"
                 | "\\xId"
                 | "\\xa"
                 | "\\xabacabad"
                 | "\\xac"
                 | "\\xad"
                 | "\\xb"
                 | "\\xc"
                 | "\\xcod"
                 | "\\xd"
                 | "\\xdom"
                 | "\\xe"
                 | "\\xf"
                 | "\\xi"
                 | "\\xlc"
                 | "\\xld"
                 | "\\xldp"
                 | "\\xlowertwocell"
                 | "\\xrightarrow"
                 | "\\xs"
                 | "\\xtwocell"
                 | "\\xuppertwocell"
                 | "\\xy"
                 | "\\xymatrix"
                 | "\\xz"
                 | "\\y"
                 | "\\zeta"
                 | "\\{"
                 | "\\}"

cartouche: CARTOUCHE_OPEN (cartouche_content | CARTOUCHE_SYMBOLS | GREEK | cartouche)* CARTOUCHE_CLOSE

cartouche_content: (CARTOUCHE_TEXT | cartouche)*

// General Isabelle tokens
OUTER_COMMENT: /\(\*[\s\S]*?\*\)/   // Multiline comments
BOTTOM: "\\<bottom>"
EQUIV: "\\<equiv>"
NEWLINE: "\\<newline>"
COMMENT_CARTOUCHE: "\\<comment>"
MARKER: "\\<^marker>"

// Greek symbols
GREEK: "\\<alpha>"
     | "\\<beta>"
     | "\\<gamma>"
     | "\\<delta>"
     | "\\<epsilon>"
     | "\\<zeta>"
     | "\\<eta>"
     | "\\<theta>"
     | "\\<iota>"
     | "\\<kappa>"
     | "\\<mu>"
     | "\\<nu>"
     | "\\<xi>"
     | "\\<pi>"
     | "\\<rho>"
     | "\\<sigma>"
     | "\\<tau>"
     | "\\<upsilon>"
     | "\\<phi>"
     | "\\<chi>"
     | "\\<psi>"
     | "\\<omega>"
     | "\\<Gamma>"
     | "\\<Delta>"
     | "\\<Theta>"
     | "\\<Lambda>"
     | "\\<Xi>"
     | "\\<Pi>"
     | "\\<Sigma>"
     | "\\<Upsilon>"
     | "\\<Phi>"
     | "\\<Psi>"
     | "\\<Omega>"

// Reserved Words
reserved: "Eval" | "False" | "Haskell" | "ML" | "OCaml" | "SML" | "Scala" | "True" | "abbreviation" | "also" | "and" | "apply" | "apply_end" | "arbitrary" | "assms" | "assume" | "assumes" | "at" | "axiomatization" | "begin" | "binder" | "by" | "case" | "cases" | "chapter" | "coinduct" | "consider" | "constrains" | "consts" | "context" | "corollary" | "datatype" | "declaration" | "declare" | "defer" | "define" | "defines" | "definition" | "done" | "end" | "file_prefix" | "fix" | "fixes" | "folded" | "for" | "from" | "fun" | "function" | "global_interpretation" | "have" | "hence" | "hide_class" | "hide_const" | "hide_fact" | "hide_type" | "if" | "imports" | "in" | "includes" | "induct" | "induction" | "inductive" | "infix" | "infixl" | "infixr" | "input" | "instance" | "instantiation" | "interpret" | "interpretation" | "is" | "lemma" | "lemmas" | "let" | "locale" | "method" | "module_name" | "monos" | "moreover" | "next" | "nitpick" | "no_notation" | "no_simp" | "no_syntax" | "no_translations" | "notation" | "note" | "notes" | "obtain" | "obtains" | "oops" | "open" | "opening" | "overloaded" | "paragraph" | "partial_function" | "pervasive" | "pred" | "prefer" | "presume" | "primrec" | "proof" | "proposition" | "qed" | "record" | "rule" | "schematic_goal" | "section" | "set" | "setup" | "show" | "shows" | "sorry" | "structure" | "subgoal" | "sublocale" | "subsection" | "subsubsection" | "supply" | "syntax" | "syntax_declaration" | "taking" | "text" | "then" | "theorem" | "theory" | "thus" | "translations" | "txt" | "type" | "type_synonym" | "typedecl" | "ultimately" | "unfolded" | "unfolding" | "using" | "when" | "where" | "with"

// Identifiers and strings
SHORT_IDENT: /[a-zA-Z](_?\d*[a-zA-Z_\']*)*/
LONG_IDENT: /([a-zA-Z](_?\d*[a-zA-Z\']*)*)(\.([a-zA-Z\'](_?\d*[a-zA-Z\']*)*))+/
#SYM_IDENT: /[!#$%&*+\-/<>?@^_`|~]+[a-zA-Z][a-zA-Z0-9]*/
SYM_IDENT: /[-!#$%&*+\/<>?@^_`|~]+[a-zA-Z][a-zA-Z0-9]*/
ID: /[a-zA-Z_][a-zA-Z_0-9\']*(\\<\\^sub>[a-zA-Z0-9_]*)?/
ALTSTRING: /`[^`]*`/
VERBATIM: /{\*.*\*}/
LETTER: /[a-zA-Z]/
LATIN: /[a-zA-Z]/

// Numbers and variables
NAT: /-?\d+/
SYM_FLOAT: /\d+(\.\d+)+|\.\d+/
TERM_VAR: /\?[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*/
TYPE_VAR: /'[a-zA-Z](_?\d*[a-zA-Z]*)*\.?\d*/

// Other predefined tokens
TYPE_IDENT: /'[a-zA-Z](_?\d*[a-zA-Z_\']*)*/

// Define start rule
start: theory_file

// Top-level rule
theory_file: (doc_block | marker)* theory_block (doc_block | marker)*

theory_block: "theory" name imports_opt "begin" theory "end"

imports_opt: "imports" import_list

import_list: (   QUOTED_STRING
               | name
               | comment_block )*

theory: (   goal proof_prove
          | statement
          | class_instance proof_prove
          | derive )*

statement: abbreviation
         | axiomatization_block
         | bundle
         | class
         | class_instance
         | comment_block
         | consts
         | context
         | datatype
         | declaration
         | declare
         | definition
         | doc_block
         | export_code
         | find_unused_assms
         | fun_block
         | global_interpretation proof_prove
         | hide_declarations
         | inductive
         | inductive_cases
         | instantiation
         | instantiation
         | interpretation_block
         | lemmas
         | lift_definition proof_prove
         | lifting_forget
         | lifting_update
         | locale_block
         | marker
         | method_block
         | ml
         | named_theorems
         | nitpick_params
         | nonterminal
         | notation_block
         | overloading
         | partial_function
         | primrec
         | primcorec
         | quickcheck_generator
         | quickcheck_params
         | record
         | setup_lifting
         | subclass
         | sublocale proof_prove
         | syntax
         | translations
         | type_synonym
         | typedecl
         | typedef proof_prove
         | unbundle
         | value
         | values

method_block: "method" name "=" instruction

instruction: single_instruction
           | single_instruction instruction_modifier
           | single_instruction instruction_modifier "," instruction
           | single_instruction ";" instruction
           | single_instruction "," instruction
           | "(" instruction ")"
           | "(" instruction ")" instruction_modifier

instruction_modifier: "+"
                    | "?"

single_instruction: "(" name method_args ")"
                  | "(" name method_args ")" instruction_modifier
                  | name method_args
                  | name

var_list_nosep: var var_list_nosep
              | var

assumptions_list: assumption "and" assumptions_list
                | assumption

assumption: QUOTED_STRING
          | NAT ":" QUOTED_STRING
          | ID ":" QUOTED_STRING

subgoal: "subgoal" thmbind? subgoal_prems? subgoal_params?

subgoal_prems: "premises" thmbind?

subgoal_params: "for" "..."? ("_" | name)+

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.1
#

name: "case"
    | "cases"
    | ID "." "cases"
    | "in"
    | "induct"
    | "pred"
    | QUOTED_STRING
    | "*"+
    | SYM_IDENT
    | (ID | GREEK | "\\<^sub>" | "." | "_" | NAT)+ "'"*
    | "-"
    | "\\<bottom>"
    | "\\<A>"
    | "\\<D>"
    | "\\<a>"
    | "\\<i>"

par_name: "(" name ")"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.3
#

embedded: QUOTED_STRING
        | "?"? GREEK "'"?
        | "?"? ID ("." ID)* "'"?
        | "False"
        | "True"
        | "false"
        | "true"
        | NAT
        | SYM_IDENT
        | SYM_IDENT
        | TERM_VAR
        | TYPE_IDENT
        | cartouche
        | (ID | "\\<a>" | "\\<i>") "\\<^sub>" ID

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.4
#

text: embedded

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.7
#

type: embedded

term: embedded

prop: embedded

inst: "_" | term

insts: inst*

named_inst: variable "=" (type | term)

named_insts: named_inst ("and" named_inst)*

variable: name | TERM_VAR | TYPE_IDENT | TYPE_VAR

typespec: typeargs? name

typearg: TYPE_IDENT | ID ("::" ID)?

# moved empty case to p_typespec in order to avoid parsing error
typeargs: TYPE_IDENT
        | "(" TYPE_IDENT ("," TYPE_IDENT)* ")"

typeargs_sorts: TYPE_IDENT ("::" sort)?
              | "(" TYPE_IDENT ("::" sort)? ("," TYPE_IDENT ("::" sort)?)* ")"

typespec_sorts: typeargs_sorts? name

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.6
#

sort: ID

sort_list_comma_sep: sort ("," sort)*

arity: ("(" sort_list_comma_sep ")")? sort

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.8
#

vars: var ("and" var)*

var: name+ ("::" type)? comment_block?
   | name ("::" type)? mixfix comment_block?

props: thmdecl? comment_block? (prop prop_pat?)+

prop_list_with_pat: prop prop_pat? ("and"? prop prop_pat?)*

names: ID ("and" names)?

name_list: name+

names_list: ID | ID names

prop_pat: "(" prop_pat_terms ")"

prop_pat_terms: prop_pat_term+

prop_pat_term: "is" (ID | QUOTED_STRING)

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.9
#

method_arg_atom: name
               | NAT
               | cartouche
               | "assms"
               | "*"
               | name ":"
               | "arbitrary" ":"
               | "rule" ":"
               | ID "!" ":"
               | name "." "cases"
               | name "." "induct"
               | name ("\\<^sub>" name)*
               | name "(" NAT ")"
               | name "(" NAT "," NAT ")" ":"
               | name "=" name
               | cases

method_arg: method_arg_atom
          | "(" method_args ")"
          | "[" method_args "]"

method_args: (","? method_arg)*

attributes: "[" (name args? ("," name args?)*)? "]"
          | "[" attribute ("," attribute)* "]"

attribute: "OF" thms
         | "THEN" ("[" NAT "]")? thm
         | "case" thmdecl? (name | ("(" name ("_" | name)* ")"))
         | "case_conclusion" name name*
         | "case_names" (name ("[" ("_" | name)*)"]")+
         | "cong" ("add" | "del")?
         | "consumes" NAT?
         | "folded" thms
         | "of" insts ("concl" ":" insts)? for_fixes?
         | "params" ("and" | name)*
         | "rotated" NAT?
         | "rule" "del"
         | "simp"
         | "simp" ("add" | "del")?
         | "split" ("!" | "del")?
         | "symmetric"
         | "tagged" name name
         | "trans" ("add" | "del")?
         | "unfolded" thms
         | "untagged" name
         | "where" named_insts for_fixes?
         | ("cases" | "induct" | "coinduct") ("del" | (("type" | "pred" | "set") ":" name))
         | ("intro" | "elim" | "dest") (("!" | "?")? NAT?)
         | ("intro" | "elim" | "dest") ((("!" | "?")? NAT?) | "del") ":" thms
         | code

args: arg*

arg: ID
   | cartouche
   | "False"
   | "for"
   | GREEK
   | ID "\\<^sub>" ID
   | "\\<infinity>"
   | "[" args "]"
   | "(" args ")"
   | NAT
   | QUOTED_STRING
   | SYM_IDENT
   | "True"
   | ":"

thmdecl: thmbind ":"

thmdef: thmbind "="

# TODO add altstring
thm: ((name selection?) | cartouche) attributes?
   | "[" attributes "]"

thms: thm+

thmbind: name attributes
       | name
       | attributes

selection: "(" selection_list ")"

selection_list: selection_item ("," selection_item)*

selection_item: NAT ("-" NAT?)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 3.3.10
#

for_fixes: "for" vars

multi_specs: structured_spec ("|" structured_spec)*

structured_spec: thmdecl? prop spec_prems? for_fixes?

spec_prems : "if" prop_list

prop_list: prop ("and"? prop)*

specification: vars comment_block? "where" comment_block? multi_specs

# TODO p75
antiquotation_body : ID

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.1
#

doc_block: (   "chapter"
             | "paragraph"
             | "section"
             | "subparagraph"
             | "subsection"
             | "subsubsection"
             | "text"
             | "text_raw"
             | "txt"
             | COMMENT_CARTOUCHE) (cartouche | QUOTED_STRING | ID)

comment_block: COMMENT_CARTOUCHE cartouche

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.2
#

antiquotation : "at" "{" antiquotation_body "}"
#                 | "/" "<" "^" ID ">" cartouche
#                 | cartouche

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.4
#

marker : MARKER cartouche

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 4.5
#

rules : rule
         | rule ";" rules

rule : "type" ":" name_list
        | "pred" ":" name_list
        | "set" ":" name_list
        | "rule" ":" thms

body : concatenation
        | concatenation "|" body

concatenation : atom_list
                 | atom_list "*" atom
                 | atom_list "+" atom_list

atom_list : atom
             | atom "?"
             | atom atom_list
             | atom "?" atom_list

atom : "(" ")"
        | "(" body ")"
        | ID
        | ID "." ID
        | ID "." "cases"
        | QUOTED_STRING
        | antiquotation
        | "at" QUOTED_STRING
        | "at" antiquotation
        | NEWLINE

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.2
#

context: "context" name opening? "begin" local_theory "end"
       | "context" includes? context_elem* "begin" local_theory "end"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.3
#

bundle: "bundle" name (("=" thms for_fixes?) | "begin" local_theory "end")

print_bundles: "print_bundles" "!"?

include: "include" name*

including: "including" name*

includes:  "includes" name*

opening: "opening" name*

unbundle: "unbundle" name*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.4
#

decl: name ("::" (ID | QUOTED_STRING | cartouche))? mixfix? "where" comment_block?

definition: "definition" ("(" "in" name ")")? decl? thmdecl? prop spec_prems? for_fixes?

abbreviation: "abbreviation" ("(" "in" ID ")")? mode? decl? prop for_fixes?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.5
#

axiomatization_block: "axiomatization" vars? ("where" axiomatization)?

axiomatization: axiomatization_header spec_prems? for_fixes?

axiomatization_header: thmdecl (ID | QUOTED_STRING) comment_block? ("and" comment_block? axiomatization_header)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.6
#

declaration : ("declaration" | "syntax_declaration") ("(" "pervasive" ")")? (name | cartouche)

declare : "declare" thms ("and" thms)*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.1
#

locale_expr: instance_list for_fixes?

instance_list: instance ("+" instance)*

instance: name (pos_insts | name_insts)?
        | qualifier ":" name (pos_insts | name_insts)

qualifier: name "?"?

pos_insts: ("_" | term)*

name_insts : "where" name "=" term ("and" name "=" term)*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.2
#

locale_block: "locale" name ("=" locale)? (comment_block)? ("begin" (local_theory)? "end")?

locale: context_elem+
      | opening ("+" context_elem+)?
      | locale_expr opening? ("+" context_elem+)?

context_elem: "fixes" vars
            | "constrains" (name "::" type ("and" name "::" type)*)
            | "assumes" props ("and" props)*
            | "defines" defines_list
            | "notes" notes_list
            | comment_block

props_list_and_sep: props ("and" props)*

defines_list: defines_list_element ("and" defines_list_element)*

defines_list_element: thmdecl? (ID | QUOTED_STRING) prop_pat?

notes_list: notes_list_element ("and" notes_list_element)*

notes_list_element: thmdef? thms

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.7.3
#

interpretation_block : "interpretation" locale_expr proof_prove

interpret: "interpret" locale_expr

global_interpretation: "global_interpretation" locale_expr definitions?

sublocale: "sublocale" (name ("<" | "\\<subseteq>")?)? locale_expr definitions?

definitions_item: thmdecl? name mixfix? "=" term

definitions: "defines" definitions_item ("and" definitions_item)*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.8
#

class: "class" class_spec "begin" local_theory "end"

class_spec: name "=" (name? opening? ("+" context_elem+)?)

instantiation : "instantiation" name_list_and_sep "::" arity "begin" local_theory "end"

name_list_and_sep : name "and" name_list_and_sep
                     | name

class_instance: "instance"
              | "instance" name_list_and_sep "::" arity
              | "instance" name "<" name
              | "instance" name "\\<subseteq>" name

subclass: "subclass" name

class_deps: "class_deps" (class_bounds class_bounds?)?

class_bounds: sort | ("(" sort ("|" sort)* ")")

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.9
#

consts: "consts" (name "::" type comment_block? mixfix? comment_block?)+

overloading: "overloading" spec+ "begin" local_theory "end"

spec: name ("\\<equiv>" | "==") term ("(" "unchecked" ")")?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.10
#

ml : ("ml" | "setup") (name | cartouche)

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.12.2
#

typedecl : "typedecl" typespec mixfix?

type_synonym : "type_synonym" typespec "=" (ID | QUOTED_STRING) mixfix?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.13
#

lemmas: "lemmas" (thmdef? thms) ("and" thmdef? thms)* for_fixes?

named_theorems: "named_theorems" (name text?) ("and" name text?)*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 5.15
#


hide_declarations : "hide_class" ("(" "open" ")")? name_list
                  | "hide_type" ("(" "open" ")")? name_list
                  | "hide_const" ("(" "open" ")")? name_list
                  | "hide_fact" ("(" "open" ")")? name_list

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.1.3
#

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.1
#

fix : "fix" vars

assume: "assume" concl (prems)? (for_fixes)?
      | "presume" concl (prems)? (for_fixes)?

concl : props ("and" props)*

# TODO should be props'_list in first line instead, but don't find
prems: "if" (props ("and" props)*)
     | "define" vars "where" props ("and" props)* for_fixes?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.2
#

let: "let" let_statement ("and" let_statement)*

let_statement: term ("and" term)* "=" term

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.3
#

proof_state: "also" ("(" thms ")")? proof_state
           | "defer" NAT? proof_state
           | "done"
           | "done" local_theory
           | "done" proof_state
           | "done" theory
           | "moreover" proof_state
           | "next" proof_state
           | "oops"
           | "oops" theory
           | "then" proof_chain
           | "ultimately" proof_chain
           | "{" proof_state "}" proof_state
           | assume proof_state
           | case proof_state
           | consider proof_prove
           | doc_block proof_state
           | fix proof_state
           | "finally" ("(" thms ")")? proof_chain
           | from proof_chain
           | have proof_prove
           | hence proof_prove
           | interpret proof_prove
           | include proof_state
           | let proof_state
           | note proof_state
           | note proof_state
           | obtain proof_prove
           | prems proof_state
           | proof proof_state
           | qed
           | qed proof_state
           | show proof_prove
           | subgoal proof_prove
           | terminal_proof_steps
           | thus proof_prove
           | unfolding proof_prove
           | using proof_prove
           | with proof_chain

proof_state_statements : proof_state_statement
                      | proof_state_statement "and" proof_state_statements

proof_state_statement : thmdef
                     | thmdef thms

proof_chain: consider proof_prove
           | have proof_prove
           | interpret proof_prove
           | obtain proof_prove
           | show proof_prove
           | subgoal proof_prove
           | "defer" NAT? proof_chain

note: "note" (thmdef? thm+) ("and" thmdef? thm+)*

from: "from" thm ("and"? thm)*

with: "with" thm ("and"? thm)*

using: "using" thm ("and"? thm)*

unfolding: "unfolding" thm ("and"? thm)*

# TODO the first line is adhoc based on AFP, and doesn't match the grammar
# "class_instance proof_prove" not allowed in Isabelle/Isar grammar, but found in AFP
local_theory: (   goal proof_prove
                | statement
                | declare
                | doc_block
                | class_instance
                | class_instance proof_prove
                | termination proof_prove
                | print_bundles context )*

# "note" "also" proof_state here contradicts grammar in Isabelle/Isar
proof_prove: "show" stmt cond_stmt?
           | "also" proof_state
           | "defer" NAT? proof_prove
           | "done"
           | "done" proof_state
           | "hence" stmt cond_stmt? for_fixes?
           | "oops"
           | "show" stmt cond_stmt? for_fixes?
           | apply proof_prove
           | by
           | by proof_state
           | doc_block proof_prove
           | including proof_prove
           | nitpick proof_prove
           | prefer_block
           | prefer_block proof_prove
           | proof
           | proof proof_state
           | qed
           | qed proof_state
           | quickcheck proof_prove
           | subgoal proof_prove
           | supply_block
           | supply_block proof_prove
           | terminal_proof_steps
           | terminal_proof_steps proof_state
           | termination proof_prove
           | unfolding proof_prove
           | using
           | using proof_prove
           | with proof_chain

# QUOTED_STRING only found in AFP, not in Isabelle/Isar grammar
conclusion: "shows" stmt
          | "obtains" obtain_clauses

obtain_clauses: obtain_case
              | par_name obtain_case
              | par_name obtain_case "|" obtain_clauses
              | obtain_case "|" obtain_clauses

obtain_case : obtain_case_statements
               | vars "where" obtain_case_statements

obtain_case_statements : obtain_case_statement
                          | obtain_case_statement "and" obtain_case_statements

obtain_case_statement : prop_list
                         | thmdecl prop_list

# no rail road diagram
assms : "assms"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.2.4
#

goal: ("lemma" | "theorem" | "corollary" | "proposition" | "schematic_goal") ("(" "in" name ")")? (long_statement | short_statement)

have: "have" stmt cond_stmt? for_fixes?

show: "show" stmt cond_stmt? for_fixes?

hence: "hence" stmt cond_stmt? for_fixes?

thus: "thus" stmt cond_stmt? for_fixes?

stmt: props ("and" props)*

cond_stmt: ("if" | "when") stmt

short_statement: stmt ("if" stmt)? for_fixes?

long_statement: thmdecl? comment_block? statement_context conclusion

statement_context: includes? context_elem*

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.3
#


#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.1
#

# TODO missing induct, induction, and coinduct
method: "(" methods ")" method_modifier? attributes?
      | name method_modifier? attributes?
      | "-"
      | "case_tac" goal_spec? term rule?
      | "fact" thms?
      | "goal_cases" name*
      | "ind_cases" prop+ for_fixes?
      | "induct_tac" goal_spec? (insts ("and" insts)*)? rule?
      | "rule" thm*
      | "split" thm*
      | "subproofs" method
      | "subst" ("(" "asm" ")")? ("(" NAT+ ")")? thm
      | "use" thms+ "in" method
      | ("simp" | "simp_all") opt? simpmod?
      | cases

opt: "(" ("no_asm" | "no_asm_simp" | "no_asm_use" | "asm_lr") ")"

simpmod: ("add" | "del" | "flip" | "only" | ("split" ("!" | "del")?) | ("cong" ("add" | "del")?)) ":" thms

method_modifier: "?" | "+" | "[" NAT "]"

method_name: name

methods: (method | (method_name method_args?)) (("," | ";" | "|") (method | (method_name method_args?)))*

goal_spec: "[" ((NAT ("-" NAT?)?) | "!") "]"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.4.2
#

proof: "proof" SYM_IDENT? method?

qed: "qed" method?

by: "by" method method?

terminal_proof_steps: "." | ".." | "sorry"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.5.1


case: "case" thmdecl? (name | ("(" name ("_" | name)* ")"))

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.5.2
#

cases: "cases" no_simp_block insts_list_and_sep rule
     | "cases" no_simp_block rule
     | "cases" no_simp_block insts_list_and_sep
     | "cases" no_simp_block
     | "cases" insts_list_and_sep rule
     | "cases" insts_list_and_sep
     | "cases" QUOTED_STRING rule
     | "cases" QUOTED_STRING
     | "cases" rule
     | "cases"

insts_list_and_sep : insts "and" insts_list_and_sep
                      | insts

no_simp_block : "(" "no_simp" ")"

arbitary_block : arbitrary

arbitrary : "arbitrary" ":" term_list_and

term_list_and : term
              | term "and" term_list_and

taking: "taking" ":" insts

rule_block : rule

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 6.6
#

consider: "consider" obtain_clauses

obtain: "obtain" (vars "where")? (par_name)? concl (prems)? (for_fixes)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 7.1
#

apply : "apply" method
      | "apply_end" method

supply_block : "supply" proof_state_statements

prefer_block : "prefer" NAT

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.2
#

mixfix: "(" template prios? NAT? ")"
      | "(" ("infix" | "infixl" | "infixr") template NAT ")"
      | "(" "binder" template prio? NAT ")"
      | "(" "structure" ")"

template : QUOTED_STRING
         | cartouche

prios : "[" NAT ("," NAT)* "]"

prio : "[" NAT "]"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.3
#

notation_block : "notation" notation_list
               | "notation" mode notation_list
               | "no_notation" notation_list
               | "no_notation" mode notation_list

notation_list : notation
              | notation "and" notation_list

notation : name mixfix

# TODO
mode: ID
    | "(" "input" ")"
    | "(" "ASCII" ")"

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 8.5.2
#

nonterminal: "nonterminal" name ("and" name)*

syntax : "syntax" mode? constdecl_list*
       | "no_syntax" mode? constdecl_list*

translations : ("translations" | "no_translations") (transpat ("==" | "=>" | "<=" | "\\<rightleftharpoons>" | "\\<leftharpoons>" | "\\<rigtharpoons>") transpat)*

transpat : QUOTED_STRING
         | "(" name ")" QUOTED_STRING

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 9.2.1
#

folded : "folded" thms
       | "unfolded" thms

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.1
#

inductive : ("inductive" | "inductive_set" | "coinductive" | "coinductive_set") ("(" "in" name ")")? vars for_fixes? ("where" multi_specs)? ("monos" thms)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.2
#

primrec: "primrec" ("(" "transfer" ")")? specification

primcorec: "primcorec" ("(" "transfer" ")")? specification

fun_block: "fun" opts? specification
         | ("function" | "nominal_function") opts? specification proof_prove

opts: "(" ("sequential" | "domintros") ("," ("sequential" | "domintros"))* ")"

termination: "termination" term? proof_prove
           | "nominal_termination" ("(" name ")")? term? proof_prove

# TODO generated from examples
datatype: "datatype" generic_type "=" constructors

generic_type : (type | ("(" type ("," type)*")")) name?

constructors : constructor ("|" constructor)*

constructor : comment_block? ID TYPE_IDENT mixfix? comment_block?
            | comment_block? (name | cartouche)+ mixfix? comment_block?
            | comment_block? (name | cartouche) "(" cartouche ")" mixfix? comment_block?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.2.2
#

partial_function: "partial_function" "(" name ")" specification

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.6.2
#

record: "record" overloaded typespec_sorts "=" type "+" constdecl_list
      | "record" typespec_sorts "=" type "+" constdecl_list
      | "record" overloaded typespec_sorts "=" constdecl_list
      | "record" typespec_sorts "=" constdecl_list

constdecl_list: constdecl
              | constdecl constdecl_list

constdecl: name "::" type
         | name "::" type comment_block
         | name "::" type mixfix

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.7
#

typedef: "typedef" overloaded? abs_type "=" rep_set

overloaded: "(" "overloaded" ")"

abs_type: typespec_sorts mixfix?

rep_set: term ("morphisms"? name name)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 11.9.2
#

setup_lifting: "setup_lifting" thm thm? ("parametric" thm)?

lift_definition: "lift_definition" ("(" "code_dt" ")")? name "::" type mixfix? "is" term ("parametric" thm*)?

lifting_forget: "lifting_forget" name

lifting_update: "lifting_update" name

lifting_restore: "lifting_restore" thm (thm thm)?

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 12.2
#

value: "value" ("[" name "]")? modes? term

values: "values" modes? NAT? term

quickcheck: "quickcheck" ("[" args "]")? NAT?

nitpick: "nitpick" ("[" args "]")? NAT?

quickcheck_params: "quickcheck_params" ("[" param_args "]")?

nitpick_params: "nitpick_params" ("[" param_args "]")?

quickcheck_generator: "quickcheck_generator" name "operations:" term*

find_unused_assms: "find_unused_assms" name?

modes: "(" name* ")"

param_args: param_arg ("," param_arg)*

param_arg: name "=" param_arg_value
         | "show_all"

param_arg_value: embedded

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 12.9
#

inductive_cases: "inductive_cases" (thmdecl? prop+ ("and" thmdecl? prop+)*)

#
# https://isabelle.in.tum.de/doc/isar-ref.pdf Section 13
#

export_code : "open" const_expr_list export_target_list
            | const_expr_list export_target_list

const_expr_list : const_expr
                | const_expr const_expr_list

export_target_list : export_target export_target_list

export_target : "in" target "module_name" ID "file_prefix" path "(" args ")"
              | "in" target "module_name" ID "file_prefix" path
              | "in" target "module_name" ID "(" args ")"
              | "in" target "module_name" ID
              | "in" target "file_prefix" path "(" args ")"
              | "in" target "file_prefix" path
              | "in" target "(" args ")"
              | "in" target

target : "SML"
       | "OCaml"
       | "Haskell"
       | "Scala"
       | "Eval"

code: "code" ("equation" | "nbe" | "abstype" | "abstract" |  "del" | "drop:" const+ | "abort:" const+)?

#
# Not covered the grammar
#

derive: "derive" "(" ID ")" ID*

const_expr : const
           | ID "." "_"
           | "_"

const : term

path : embedded
"""

# Define precedence and associativity (optional for Isabelle)
precedence = ()


# Build the parser
parser = Lark(grammar, start='start', parser='earley')


def parse(input_text):
    try:
        tree = parser.parse(input_text)
        return tree
    except Exception as e:
        print(f"Error parsing input: {e}")
