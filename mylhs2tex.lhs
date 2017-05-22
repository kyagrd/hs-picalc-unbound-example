%include colorcode.fmt
%include polycode.fmt
%include lhs2TeX.sty

\renewcommand{\onelinecommentchars}{\color{gray}\quad-{}- }
\renewcommand{\commentbeginchars}{\color{gray}\enskip\{- }
\renewcommand{\commentendchars}{-\}\enskip}

\renewcommand{\visiblecomments}{%
  \let\onelinecomment=\onelinecommentchars
  \let\commentbegin=\commentbeginchars
  \let\commentend=\commentendchars}

\renewcommand{\invisiblecomments}{%
  \let\onelinecomment=\empty
  \let\commentbegin=\empty
  \let\commentend=\empty}

\visiblecomments

%format qualified = "\mathbf{qualified}"
%format hiding = "\mathbf{hiding}"
%format as = "\mathbf{as}"

%format Var = "V\!"
%format ; = "\hspace{.2ex};\hspace{.2ex}"
%format `respects` = "\mathop{^{\,_{\backprime}\!}"respects"^{_\backprime}}"
%format '' = "\texttt{''\!''\!\!}"
%format $ = "\mathop{\texttt{\$}}"
%format subst (x) (v) = "\mathop{\sub{"x"}{"v"}\!}\!"
%format sigmaSubs = "{\hat{\sigma}}"

%format unbind = "(".\")^{{\text{-}\hspace{-.2ex}1\!}}"
%format mapM_ = mapM"\hspace{-.2ex}"_"\,"
%format sim_ = sim"\hspace{-.2ex}"_"\,"
%format bisim_ = bisim"\hspace{-.2ex}"_"\,"

%format Null = "\scalebox{1.1}{\bf\texttt{0}}"
%format TauP = "\scalebox{1.3}{$\tau\hspace{-.4ex}\raisebox{.29ex}{\textbf{.}}$}"
%format Par (a) (b) = a "\mathop{\|}" b
%format `Par` = "\mathop{\|}"
%format Plus (a) (b) = a "\mathop{.\hspace{-.6ex}{+}\hspace{-.6ex}.}" b
%format `Plus` = "\mathop{.\hspace{-.6ex}{+}\hspace{-.6ex}.}"
%format Nu = "\scalebox{1.25}{$\nu$}\!"
%format Match (a) (b) = "(" a "\mathop{{\leftrightarrow}\hspace{-1.48ex}\raisebox{.1ex}{:}\;\,}" b ")"
%format .\ =  "\hspace{.1ex}.\hspace{-.4ex}\backslash"

%format tau = "\tau"
%format tautau = "\tau\tau"

%format .+ =  "\mathop{.\hspace{-.6ex}{+}\hspace{-.6ex}.}"
%format .| =  "\mathop{\|}"

%format oneb = "\textit{one}_{\textsc{b}}"
%format oneb'
%format <|> = "\,\mathop{\scalebox{1}[.7]{\raisebox{.3ex}{$\langle\hspace{-.1ex}\vert\hspace{-.1ex}\rangle$}}}\,"
%format <*> = "\mathop{\scalebox{1}[.7]{\raisebox{.3ex}{$\langle$}}\!\!*\!\!\scalebox{1}[.7]{\raisebox{.3ex}{$\rangle$}}}"
%format <$> = "\mathop{\scalebox{1}[.7]{\raisebox{.3ex}{$\langle\hspace{-.3ex}"$"\hspace{-.3ex}\rangle$}}}"
%format <$> = "\mathop{\scalebox{1}[.7]{\raisebox{.3ex}{$\langle$}}\hspace{-.7ex}"$"\hspace{-.7ex}\scalebox{1}[.7]{\raisebox{.3ex}{$\rangle$}}}"
%format Tau = "\ensuremath{\scalebox{1.3}{$\tau$}}"
%format Up = "\MVUparrow\!"
%format Dn = "\MVDnarrow\!"
%format UpB = "\MVUparrow_{\!\textsc{b}\!}"
%format DnB = "\hspace{-.15ex}\MVDnarrow^{\hspace{-.18ex}\textsc{b}\!}"
%format PrB = "\textit{Pr}_{\textsc{b}}"
%format ActB = "\textit{Act}_{\textsc{b}}"
%format FormB = "\textit{Form}_{\textsc{b}}"
%format OneB = One"_{\textsc{b}}"
%format extendSubB = extendSub"_{\textsc{b}}"
%format returnL = return"_L"
%format returnR = return"_R"
%format TT = "\top"
%format FF = "\bot"
%format Conj = "\bigwedge\!"
%format Disj = "\bigvee\!"
%format Dia = "\Diamond\!"
%format Box = "\Box\!"
%format DiaB = "\Diamond_{^{\!}\textsc{b}}\!"
%format BoxB = "\Box_{^{\!}\textsc{b}}\!"
%format DiaMatch = "\Diamond_{\!=}\!"
%format BoxMatch = "\Box_{=}\!"
%format .= = "\leftrightarrow"
%format .: = "\mathop{\raisebox{.5ex}{$\curvearrowright$}\hspace{-1.9ex}\scalebox{.8}{$+$}\;}"
%format .++ = "\cup"

%format x1
%format x2
%format y1
%format y2
%format b1
%format b2
%format p0
%format q0
%format p1
%format p2
%format q1
%format q2
%format lp = "l_p"
%format lq = "l_q"
%format bp = "b_{\!p}"
%format bq = "b_{\!q}"
%format bp' = "b_{\!"p'"}"
%format bq' = "b_{\!"q'"}"
%format sigma = "\sigma"
%format sigma_p = sigma"_{\!p}"
%format sigma_q = sigma"_{\!q}"
%format sigma'
%format sigmaqs = sigma"_{\!q\!}"s
%format sigmaps = sigma"_{\!p\!}"s
%format nctx = "\Gamma"
%format nctx'
%format All = "\forall\hspace{-.75ex}\raisebox{.1ex}{\scalebox{1.1}[.9]{$/$}}\!"
%format Nab = "\nabla\hspace{-.83ex}\raisebox{.1ex}{\scalebox{1.1}[.9]{$/$}}\!"
%format postCB = postC"_{\textsc{b}}"
%format postCbaseB = postCbase"_{\textsc{b}}"
%format preCB = preC"_{\textsc{B}}"
%format preCbaseB = preCbase"_{\textsc{b}}"
%format subsMatchingActB = subsMatchingAct"_{\textsc{b}}"
%format dfsL = dfs"_{\!L}"
%format dfsR = dfs"_{\!R}"
%format rsL = rs"_{\!L}"
%format rsR = rs"_{\!R}"
%format left1Bs = left1"{\scriptsize\textsc{b}}"s
%format right1Bs = right1"{\scriptsize\textsc{b}}"s
