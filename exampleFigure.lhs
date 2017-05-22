\begin{figure}\small
$\begin{array}{rrl}
{\color{ACMRed}|P|}\triangleq \hspace{-2ex}&\hspace{-2ex}
 {\color{ACMRed}|TauP(TauP Null) `Plus` TauP Null|} &\hspace{-1ex}
	\models \hspace{1.25ex} \langle\tau\rangle\langle\tau\rangle\top \\
& \rotatebox[origin=c]{-90}{$\not\sim_{\!o}$}\phantom{AAA} & \\
{\color{ACMDarkBlue}|Q|}\triangleq \hspace{-2ex}&\hspace{-2ex}
 {\color{ACMDarkBlue}|Match x y (TauP (TauP Null)) `Plus` TauP Null|} &\hspace{-1ex}
	\models \hspace{1.25ex} [\tau]\big(\uwave{\langle x=y \rangle\top} \lor [\tau]\bot\big)
\end{array}
$
\begin{forest}
for tree={edge={->,line width=.75pt},l sep=4ex}
[{}, phantom, s sep=4ex
%
[{(1)}
   [{\!\!\!\!{\color{ACMRed}|TauP Null|}\,,\,{\color{ACMDarkBlue}|Q|}},edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMRed}
     [{\!\!\!\!\!\!{\color{ACMRed}|TauP Null|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,right,color=ACMDarkBlue,color=ACMDarkBlue,font=\scriptsize]{\color{ACMDarkBlue}$\begin{matrix*}[l]|[]|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMDarkBlue}
       [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|TauP Null|}\!\!\!\!\!\!}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMRed} ] ] ]
]
%
[{(2)}
   [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|Q|}\!}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMRed}
     [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,right,color=ACMDarkBlue,font=\scriptsize]{\color{ACMDarkBlue}$\begin{matrix*}[l]|[]|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMDarkBlue} ] ]
]
%
[{(3)}
   [{{\color{ACMRed}|P|}\,,\,{\color{ACMDarkBlue}|TauP Null|}\!\!\!\!\!\!}, edge label={node[midway,right,color=ACMDarkBlue,font=\scriptsize]{\color{ACMDarkBlue}$\begin{matrix*}[l]|sigma={-"\uwave{"-}[(x,y)]{-"}"-}|\\ \vspace{-4.25ex} \\|Tau|\end{matrix*}$}}, edge+={color=ACMDarkBlue}
     [{{\color{ACMRed}|TauP Null|}\,,\,{\color{ACMDarkBlue}|TauP Null|}}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|sigma|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMRed}, s sep=4.5ex
       [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|TauP Null|}\!\!\!\!\!\!}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMRed}
         [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,right,color=ACMDarkBlue,font=\scriptsize]{\color{ACMDarkBlue}$\begin{matrix*}[l]|[]|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMDarkBlue} ] ]
       [{\!\!\!\!\!\!{\color{ACMRed}|TauP Null|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,right,color=ACMDarkBlue,font=\scriptsize]{\color{ACMDarkBlue}$\begin{matrix*}[l]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMDarkBlue}
         [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|Null|}}
, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMRed} ] ]
     ]
     [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|TauP Null|}\!\!\!\!\!\!}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|sigma|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMRed}
       [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,right,color=ACMDarkBlue,font=\scriptsize]{\color{ACMDarkBlue}$\begin{matrix*}[l]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMDarkBlue} ] ]
   ]
]
%
[{(4)}
  [{{\color{ACMRed}|P|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,right,color=ACMDarkBlue,font=\scriptsize]{\color{ACMDarkBlue}$\begin{matrix*}[l]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMDarkBlue}, s sep=4.5ex
    [{{\color{ACMRed}|TauP Null|}\,,\,{\color{ACMDarkBlue}|Null|}\hspace{1ex}}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMRed}
      [{{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+={color=ACMRed} ]
    ]
    [{\!\!\!\!{\color{ACMRed}|Null|}\,,\,{\color{ACMDarkBlue}|Null|}}, edge label={node[midway,left,color=ACMRed,font=\scriptsize]{\color{ACMRed}$\begin{matrix*}[r]|[]|\\|Tau|\end{matrix*}$}}, edge+=dashed, edge+={color=ACMRed} ]
  ]
]
%
]
\end{forest}
\\[-6.25ex] \hfill
$\begin{matrix*}[l] \rightarrow \text{\scriptsize(leading step)} \\
                    \dashrightarrow \text{\scriptsize(following step)} \end{matrix*}$
\vspace*{-1.5ex}
\caption{The forest of all possible open bisimulation steps of non-bisimilar processes
and their distinguishing formulae.}
\vspace*{-1.5ex}
%{\color{gray}\hrule}
\label{fig:example}
\end{figure}

