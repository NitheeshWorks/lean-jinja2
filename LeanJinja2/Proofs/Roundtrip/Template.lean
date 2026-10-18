import LeanJinja2.Proofs.Roundtrip.Stream

/-!
# A printed template is a lexable stream

Every well-formed template prints to a `Stream`: tags whose contents are
lexable tokens with balanced brackets, and template text that is never
followed by more template text.
-/

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

/-! ## Joining streams -/

def StartsTag (b : List TokKind) : Prop := b.head? = some .varBegin ∨ b.head? = some .blockBegin

def EndsData (a : List TokKind) : Prop := ∃ s, a.getLast? = some (.data s)

theorem Stream.startsTag {b : List TokKind} (hb : Stream b) (ht : StartsTag b) :
    ∃ blk ks rest, b = openKind blk :: (ks ++ closeKind blk :: rest) ∧ InnerAll ks ∧
      stackAfter [] ks = some [] ∧ (blk = true → BlockHead ks) ∧ Stream rest := by
  cases hb with
  | nil => simp [StartsTag] at ht
  | text s _ => simp [StartsTag] at ht
  | tag pre blk ks rest hpre hin hbal hhead hrest =>
    cases pre with
    | none => exact ⟨blk, ks, rest, rfl, hin, hbal, hhead, hrest⟩
    | some s => simp [StartsTag, preTok] at ht

theorem Stream.append {a b : List TokKind} (ha : Stream a) (hb : Stream b)
    (h : EndsData a → b = [] ∨ StartsTag b) : Stream (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | text s hs =>
    rcases h ⟨s, rfl⟩ with rfl | ht
    · exact Stream.text s hs
    · obtain ⟨blk, ks, rest, rfl, hin, hbal, hhead, hrest⟩ := hb.startsTag ht
      exact Stream.tag (some s) blk ks rest hs hin hbal hhead hrest
  | tag pre blk ks rest hpre hin hbal hhead hrest ih =>
    have := Stream.tag pre blk ks (rest ++ b) hpre hin hbal hhead (ih (fun hd => h (by
      obtain ⟨s, hs⟩ := hd
      refine ⟨s, ?_⟩
      have heq : preTok pre ++ openKind blk :: (ks ++ closeKind blk :: rest) =
          (preTok pre ++ openKind blk :: ks ++ [closeKind blk]) ++ rest := by simp
      rw [heq, List.getLast?_append, hs]; rfl)))
    simpa using this

/-- Tag contents the lexer reads back. -/
def LexOK (ks : List TokKind) : Prop := InnerAll ks ∧ Bal ks

theorem LexOK.stack {ks : List TokKind} (h : LexOK ks) : stackAfter [] ks = some [] := by
  have := h.2 [] []; simpa [stackAfter] using this

theorem Stream.tagThen (blk : Bool) {ks c : List TokKind} (hk : LexOK ks) (hh : blk = true → BlockHead ks)
    (hc : Stream c) : Stream (openKind blk :: (ks ++ closeKind blk :: c)) := by
  simpa [preTok] using Stream.tag none blk ks c trivial hk.1 hk.stack hh hc

theorem Stream.block {ks c : List TokKind} (hk : LexOK ks) (hh : BlockHead ks) (hc : Stream c) :
    Stream (Pretty.tag ks ++ c) := by
  simpa [Pretty.tag, openKind, closeKind] using Stream.tagThen true hk (fun _ => hh) hc

theorem startsTag_tag (ks c : List TokKind) : StartsTag (Pretty.tag ks ++ c) := by
  simp [StartsTag, Pretty.tag]

theorem startsTag_tag' (ks : List TokKind) : StartsTag (Pretty.tag ks) := by
  simp [StartsTag, Pretty.tag]

/-! ## Tag contents -/

theorem lexOK_append {a b : List TokKind} (ha : LexOK a) (hb : LexOK b) : LexOK (a ++ b) :=
  ⟨innerAll_append.mpr ⟨ha.1, hb.1⟩, fun st r => by rw [List.append_assoc, ha.2, hb.2]⟩

theorem lexOK_nil : LexOK [] := ⟨by simp, bal_nil⟩

theorem lexOK_name {s : String} (h : IsIdent s) : LexOK [.name s] :=
  ⟨by simpa [InnerTok] using h, fun st r => by simp [stackStep]⟩

theorem lexOK_op {o : Op} (h1 : closerOf o = none) (h2 : isCloser o = none) : LexOK [.op o] :=
  ⟨by simp [InnerTok], fun st r => by simp [stackStep, h1, h2]⟩

theorem lexOK_paren {X : List TokKind} (h : LexOK X) : LexOK ([.op .lparen] ++ X ++ [.op .rparen]) :=
  ⟨by simp [InnerTok, h.1], fun st r => by simp [stackStep, closerOf, isCloser, h.2]⟩

theorem lexOK_expr {e : Expr} (h : e.WF) : LexOK (Pretty.expr e) := ⟨expr_inner e h, expr_bal e⟩

theorem lexOK_target_plain {t : Target} (hp : t.Plain) : LexOK (Pretty.target t) := by
  rw [Target.print_eq _ hp]
  exact lexOK_expr (Target.toExpr_WF _ hp)

theorem lexOK_target {t : Target} (h : t.Settable) : LexOK (Pretty.target t) := by
  cases t with
  | nsAttr n a =>
    simp only [Target.Settable] at h
    simpa [Pretty.target] using lexOK_append (lexOK_name h.1.1)
      (lexOK_append (lexOK_op (o := .dot) rfl rfl) (lexOK_name h.2.1))
  | name n => exact lexOK_target_plain (by simpa [Target.Settable] using h)
  | tuple ts => exact lexOK_target_plain (by simpa [Target.Settable] using h)

theorem lexOK_params : ∀ (had : Bool) (ps : List Param), ParamsWF had ps → LexOK (Pretty.params ps)
  | _, [], _ => by simpa [Pretty.params] using lexOK_nil
  | had, (p, d) :: ps, hw => by
    simp only [ParamsWF] at hw
    obtain ⟨hp, hd, -, hps⟩ := hw
    have h1 : LexOK (Pretty.param (p, d)) := by
      cases d with
      | none => simpa [Pretty.param] using lexOK_name hp.1
      | some e =>
        simpa [Pretty.param] using lexOK_append (lexOK_name hp.1) (lexOK_append (lexOK_op (o := .assign) rfl rfl) (lexOK_expr (by simpa [Expr.WFOpt] using hd)))
    cases ps with
    | nil => simpa [Pretty.params] using h1
    | cons q qs =>
      have ih := lexOK_params _ (q :: qs) hps
      have : Pretty.params ((p, d) :: q :: qs) = Pretty.param (p, d) ++ [.op .comma] ++ Pretty.params (q :: qs) := by
        simp [Pretty.params]
      rw [this]
      exact lexOK_append (lexOK_append h1 (lexOK_op (o := .comma) rfl rfl)) ih

theorem lexOK_args {args : List Expr} {kw : List (String × Expr)} (ha : Expr.WFs args) (hk : Expr.WFKw kw) :
    LexOK (Pretty.parenArgs (Pretty.exprs args) (Pretty.kwargs kw)) :=
  ⟨innerAll_parenArgs (exprs_inner args ha) (kwargs_inner kw hk), bal_parenArgs (exprs_bal args) (kwargs_bal kw)⟩

theorem lexOK_filterCall {f : FilterCall} (h : f.WF) : LexOK (Pretty.filterCall f) :=
  lexOK_append (lexOK_name h.1.1) (lexOK_args h.2.1 h.2.2)

theorem lexOK_chain : ∀ (fs : List FilterCall), (∀ f ∈ fs, f.WF) → LexOK (Pretty.filterChain fs)
  | [], _ => by simpa [Pretty.filterChain] using lexOK_nil
  | [f], h => by simpa [Pretty.filterChain] using lexOK_filterCall (h f (by simp))
  | f :: g :: gs, h => by
    have ih := lexOK_chain (g :: gs) (fun x hx => h x (by simp_all))
    have : Pretty.filterChain (f :: g :: gs) = Pretty.filterCall f ++ [.op .pipe] ++ Pretty.filterChain (g :: gs) := by
      simp [Pretty.filterChain]
    rw [this]
    exact lexOK_append (lexOK_append (lexOK_filterCall (h f (by simp))) (lexOK_op (o := .pipe) rfl rfl)) ih

theorem lexOK_pipes : ∀ (fs : List FilterCall), (∀ f ∈ fs, f.WF) →
    LexOK (fs.flatMap fun f => [Pretty.op .pipe] ++ Pretty.filterCall f)
  | [], _ => by simpa using lexOK_nil
  | f :: fs, h => by
    rw [List.flatMap_cons]
    exact lexOK_append (lexOK_append (lexOK_op (o := .pipe) rfl rfl) (lexOK_filterCall (h f (by simp))))
      (lexOK_pipes fs (fun x hx => h x (by simp [hx])))

theorem lexOK_assigns : ∀ (as : List (Target × Expr)), Node.AssignsWF as → LexOK (Pretty.assigns as)
  | [], _ => by simpa [Pretty.assigns] using lexOK_nil
  | (t, e) :: as, hw => by
    simp only [Node.AssignsWF] at hw
    obtain ⟨ht, he, has⟩ := hw
    have ht' : t.Settable := by cases t <;> simp_all [Target.Settable, Target.Plain]
    have h1 := lexOK_append (lexOK_target ht') (lexOK_append (lexOK_op (o := .assign) rfl rfl) (lexOK_expr he))
    cases as with
    | nil => simpa [Pretty.assigns] using h1
    | cons a as' =>
      have ih := lexOK_assigns (a :: as') has
      obtain ⟨a1, a2⟩ := a
      have : Pretty.assigns ((t, e) :: (a1, a2) :: as') =
          (Pretty.target t ++ [.op .assign] ++ Pretty.expr e) ++ [.op .comma] ++ Pretty.assigns ((a1, a2) :: as') := by
        simp [Pretty.assigns]
      rw [this]
      exact lexOK_append (lexOK_append (by simpa using h1) (lexOK_op (o := .comma) rfl rfl)) ih

end LeanJinja2

namespace LeanJinja2

open Lex

set_option linter.unusedSimpArgs false

/-! ## Nodes -/

theorem lexOK_kw (s : String) (h : identB s = true := by decide) : LexOK [.name s] :=
  lexOK_name (IsIdent.of_identB h)

theorem blockHead_kw (kw : String) (r : List TokKind) (h : kw.toList.head? ≠ some 'r' := by decide) :
    BlockHead (.name kw :: r) := ⟨kw, r, rfl, h⟩

theorem endTag_stream (kw : String) (h1 : identB kw = true := by decide) (h2 : kw.toList.head? ≠ some 'r' := by decide) :
    Stream (Pretty.tag [Pretty.nm kw]) := by
  simpa using Stream.block (lexOK_kw kw h1) (blockHead_kw kw [] h2) Stream.nil

theorem Stream.thenTag {a c : List TokKind} (ha : Stream a) (hc : Stream c) (ht : StartsTag c) :
    Stream (a ++ c) := Stream.append ha hc (fun _ => Or.inr ht)

theorem node_last (nd : Node) (h : nd.isText = false) : ¬ EndsData (Pretty.node nd) := by
  rintro ⟨s, hs⟩
  cases nd with
  | text _ => simp [Node.isText] at h
  | if_ bs els =>
    cases bs with
    | nil => simp [Pretty.node, Pretty.tag, List.getLast?_append, List.getLast?_cons] at hs
    | cons b bs => obtain ⟨t, b⟩ := b; simp [Pretty.node, Pretty.tag, List.getLast?_append, List.getLast?_cons] at hs
  | _ => simp [Pretty.node, Pretty.tag, List.getLast?_append, List.getLast?_cons] at hs

theorem node_starts (nd : Node) (h : nd.isText = false) : StartsTag (Pretty.node nd) := by
  cases nd with
  | text _ => simp [Node.isText] at h
  | if_ bs els =>
    cases bs with
    | nil => simp [StartsTag, Pretty.node, Pretty.tag]
    | cons b bs => obtain ⟨t, b⟩ := b; simp [StartsTag, Pretty.node, Pretty.tag]
  | _ => simp [StartsTag, Pretty.node, Pretty.tag]

theorem startsTag_append {a b : List TokKind} (h : StartsTag a) : StartsTag (a ++ b) := by
  unfold StartsTag at *
  cases a with
  | nil => simp at h
  | cons x xs => simpa using h

theorem lexOK_ctx (wc : Bool) : LexOK [Pretty.nm (if wc then "with" else "without"), Pretty.nm "context"] := by
  cases wc
  · simpa using lexOK_append (lexOK_kw "without") (lexOK_kw "context")
  · simpa using lexOK_append (lexOK_kw "with") (lexOK_kw "context")

theorem lexOK_importName (p : String × Option String) (h : ImportNameWF p) :
    LexOK (Pretty.importName p) := by
  obtain ⟨n, a⟩ := p
  obtain ⟨hn, -, ha⟩ := h
  cases a with
  | none => exact lexOK_name hn.1
  | some a =>
    simpa [Pretty.importName] using
      lexOK_append (lexOK_append (lexOK_name hn.1) (lexOK_kw "as")) (lexOK_name (ha a rfl).1)

theorem lexOK_importNames : (names : List (String × Option String)) → (∀ p ∈ names, ImportNameWF p) →
    LexOK (Pretty.importNames names)
  | [], _ => lexOK_nil
  | [p], h => lexOK_importName p (h p (by simp))
  | p :: q :: qs, h => by
    have := lexOK_append (lexOK_append (lexOK_importName p (h p (by simp))) (lexOK_op (o := .comma) rfl rfl))
      (lexOK_importNames (q :: qs) (fun r hr => h r (by simp_all)))
    simpa [Pretty.importNames, Pretty.op, List.append_assoc] using this

mutual
theorem node_stream : (nd : Node) → nd.WF → Stream (Pretty.node nd)
  | .text s, hw => by simpa [Pretty.node] using Stream.text s hw
  | .output e, hw => by
    simpa [Pretty.node, preTok, openKind, closeKind] using
      Stream.tag none false (Pretty.expr e) [] trivial (lexOK_expr hw).1 (lexOK_expr hw).stack (by simp) Stream.nil
  | .if_ [] _, hw => by simp [Node.WF] at hw
  | .if_ ((t, b) :: bs) els, hw => by
    simp only [Node.WF, Node.BranchesWF] at hw
    obtain ⟨_, ⟨ht, hb, hbs⟩, hels⟩ := hw
    have hend := endTag_stream "endif"
    have hE := elsePart_stream els hels hend (startsTag_tag' _)
    have hEl : Stream (Pretty.elifs bs ++ ((if els.isEmpty then [] else Pretty.tag [Pretty.nm "else"] ++
        Pretty.nodes els) ++ Pretty.tag [Pretty.nm "endif"])) :=
      Stream.append (elifs_stream bs hbs) hE.1 (fun _ => Or.inr hE.2)
    have hstart : StartsTag (Pretty.elifs bs ++ ((if els.isEmpty then [] else Pretty.tag [Pretty.nm "else"] ++
        Pretty.nodes els) ++ Pretty.tag [Pretty.nm "endif"])) := by
      cases bs with
      | nil => simpa [Pretty.elifs] using hE.2
      | cons b' bs' => obtain ⟨t', b'⟩ := b'; simp [StartsTag, Pretty.elifs, Pretty.tag]
    have := Stream.block (lexOK_append (lexOK_kw "if") (lexOK_expr ht)) (blockHead_kw "if" _)
      (Stream.thenTag (nodes_stream b hb) hEl hstart)
    simpa [Pretty.node, List.append_assoc] using this
  | .for_ t it fl rc body els, hw => by
    simp only [Node.WF] at hw
    obtain ⟨ht, hit, hfl, hb, hels⟩ := hw
    have hE := elsePart_stream els hels (endTag_stream "endfor") (startsTag_tag' _)
    have hfilt' : ∀ fl' : Option Expr, Expr.WFOpt fl' →
        LexOK (match fl' with | some f => [Pretty.nm "if"] ++ Pretty.expr f | none => []) := by
      intro fl' h'
      cases fl' with
      | none => exact lexOK_nil
      | some f => exact lexOK_append (lexOK_kw "if") (lexOK_expr (by simpa [Expr.WFOpt] using h'))
    have hfilt := hfilt' fl hfl
    have hrec : LexOK (if rc then [Pretty.nm "recursive"] else []) := by
      cases rc
      · exact lexOK_nil
      · exact lexOK_kw "recursive"
    have hk := lexOK_append (lexOK_append (lexOK_append (lexOK_append (lexOK_append (lexOK_kw "for")
      (lexOK_target_plain ht)) (lexOK_kw "in")) (lexOK_expr hit)) hfilt) hrec
    have := Stream.block hk (by simpa using blockHead_kw "for" _) (Stream.thenTag (nodes_stream body hb) hE.1 hE.2)
    cases fl <;> simpa [Pretty.node, List.append_assoc] using this
  | .set t e, hw => by
    simp only [Node.WF] at hw
    have hk := lexOK_append (lexOK_append (lexOK_append (lexOK_kw "set") (lexOK_target hw.1))
      (lexOK_op (o := .assign) rfl rfl)) (lexOK_expr hw.2)
    have := Stream.block hk (by simpa using blockHead_kw "set" _) Stream.nil
    simpa [Pretty.node, List.append_assoc] using this
  | .setBlock t fs body, hw => by
    simp only [Node.WF] at hw
    obtain ⟨ht, hfs, hb⟩ := hw
    have hk := lexOK_append (lexOK_append (lexOK_kw "set") (lexOK_target ht)) (lexOK_pipes fs hfs)
    have := Stream.block hk (by simpa using blockHead_kw "set" _)
      (Stream.thenTag (nodes_stream body hb) (endTag_stream "endset") (startsTag_tag' _))
    simpa [Pretty.node, List.append_assoc] using this
  | .macro n ps body, hw => by
    simp only [Node.WF] at hw
    obtain ⟨hn, hps, hb⟩ := hw
    have hk' : LexOK ([Pretty.nm "macro", Pretty.nm n, Pretty.op .lparen] ++ Pretty.params ps ++ [Pretty.op .rparen]) := by
      refine ⟨?_, fun st r => ?_⟩
      · simp [InnerTok, (lexOK_params false ps hps).1, hn.1]
      · have hb2 := (lexOK_params false ps hps).2
        simp [stackStep, closerOf, isCloser, hb2]
    have := Stream.block hk' (by simpa using blockHead_kw "macro" _)
      (Stream.thenTag (nodes_stream body hb) (endTag_stream "endmacro") (startsTag_tag' _))
    simpa [Pretty.node, List.append_assoc] using this
  | .callBlock ps c body, hw => by
    simp only [Node.WF] at hw
    obtain ⟨hps, -, hc, hb⟩ := hw
    have hk' : LexOK ([Pretty.nm "call", Pretty.op .lparen] ++ Pretty.params ps ++ [Pretty.op .rparen] ++
        Pretty.expr c) := by
      refine ⟨?_, fun st r => ?_⟩
      · simp [InnerTok, (lexOK_params false ps hps).1, (lexOK_expr hc).1]
      · have hb2 := (lexOK_params false ps hps).2
        have hb3 := (lexOK_expr hc).2
        simp [stackStep, closerOf, isCloser, hb2, hb3]
    have := Stream.block hk' (by simpa using blockHead_kw "call" _)
      (Stream.thenTag (nodes_stream body hb) (endTag_stream "endcall") (startsTag_tag' _))
    simpa [Pretty.node, List.append_assoc] using this
  | .include e ig wc, hw => by
    simp only [Node.WF] at hw
    have hig : LexOK (if ig then [Pretty.nm "ignore", Pretty.nm "missing"] else []) := by
      cases ig
      · exact lexOK_nil
      · simpa using lexOK_append (lexOK_kw "ignore") (lexOK_kw "missing")
    have hwc : LexOK [Pretty.nm (if wc then "with" else "without"), Pretty.nm "context"] := by
      cases wc
      · simpa using lexOK_append (lexOK_kw "without") (lexOK_kw "context")
      · simpa using lexOK_append (lexOK_kw "with") (lexOK_kw "context")
    have hk := lexOK_append (lexOK_append (lexOK_append (lexOK_kw "include") (lexOK_expr hw)) hig) hwc
    have := Stream.block hk (by simpa using blockHead_kw "include" _) Stream.nil
    simpa [Pretty.node, List.append_assoc] using this
  | .extends e, hw => by
    simp only [Node.WF] at hw
    have := Stream.block (lexOK_append (lexOK_kw "extends") (lexOK_expr hw)) (by simpa using blockHead_kw "extends" _)
      Stream.nil
    simpa [Pretty.node, List.append_assoc] using this
  | .import_ e t wc, hw => by
    simp only [Node.WF] at hw
    have hk := lexOK_append (lexOK_append (lexOK_append (lexOK_append (lexOK_kw "import") (lexOK_expr hw.1))
      (lexOK_kw "as")) (lexOK_name hw.2.1)) (lexOK_ctx wc)
    have := Stream.block hk (by simpa using blockHead_kw "import" _) Stream.nil
    simpa [Pretty.node, List.append_assoc] using this
  | .fromImport e names wc, hw => by
    simp only [Node.WF] at hw
    have hk := lexOK_append (lexOK_append (lexOK_append (lexOK_append (lexOK_kw "from") (lexOK_expr hw.1))
      (lexOK_kw "import")) (lexOK_importNames names hw.2)) (lexOK_ctx wc)
    have := Stream.block hk (by simpa using blockHead_kw "from" _) Stream.nil
    simpa [Pretty.node, List.append_assoc] using this
  | .block n sc req body, hw => by
    simp only [Node.WF] at hw
    obtain ⟨hn, hb, -⟩ := hw
    have hsc : LexOK (if sc then [Pretty.nm "scoped"] else []) := by
      cases sc
      · exact lexOK_nil
      · exact lexOK_kw "scoped"
    have hrq : LexOK (if req then [Pretty.nm "required"] else []) := by
      cases req
      · exact lexOK_nil
      · exact lexOK_kw "required"
    have hk := lexOK_append (lexOK_append (lexOK_append (lexOK_kw "block") (lexOK_name hn.1)) hsc) hrq
    have := Stream.block hk (by simpa using blockHead_kw "block" _)
      (Stream.thenTag (nodes_stream body hb) (endTag_stream "endblock") (startsTag_tag' _))
    simpa [Pretty.node, List.append_assoc] using this
  | .with_ as body, hw => by
    simp only [Node.WF] at hw
    have hk := lexOK_append (lexOK_kw "with") (lexOK_assigns as hw.1)
    have := Stream.block hk (by simpa using blockHead_kw "with" _)
      (Stream.thenTag (nodes_stream body hw.2) (endTag_stream "endwith") (startsTag_tag' _))
    simpa [Pretty.node, List.append_assoc] using this
  | .filterBlock fs body, hw => by
    simp only [Node.WF] at hw
    have hk := lexOK_append (lexOK_kw "filter") (lexOK_chain fs hw.2.1)
    have := Stream.block hk (by simpa using blockHead_kw "filter" _)
      (Stream.thenTag (nodes_stream body hw.2.2) (endTag_stream "endfilter") (startsTag_tag' _))
    simpa [Pretty.node, List.append_assoc] using this
  | .autoescape e body, hw => by
    simp only [Node.WF] at hw
    have hk := lexOK_append (lexOK_kw "autoescape") (lexOK_expr hw.1)
    have := Stream.block hk (by simpa using blockHead_kw "autoescape" _)
      (Stream.thenTag (nodes_stream body hw.2) (endTag_stream "endautoescape") (startsTag_tag' _))
    simpa [Pretty.node, List.append_assoc] using this

theorem nodes_stream : (b : List Node) → Node.BodyWF b → Stream (Pretty.nodes b)
  | [], _ => by simpa [Pretty.nodes] using Stream.nil
  | nd :: ns, hw => by
    simp only [Node.BodyWF] at hw
    obtain ⟨hnd, hns, htxt⟩ := hw
    rw [Pretty.nodes]
    refine Stream.append (node_stream nd hnd) (nodes_stream ns hns) (fun hd => ?_)
    cases hti : nd.isText with
    | false => exact absurd hd (node_last nd hti)
    | true =>
      cases ns with
      | nil => exact Or.inl (by simp [Pretty.nodes])
      | cons m ms =>
        have hm : m.isText = false := by
          have := htxt hti; simp at this; simpa using this
        right; rw [Pretty.nodes]; exact startsTag_append (node_starts m hm)

theorem elifs_stream : (bs : List (Expr × List Node)) → Node.BranchesWF bs → Stream (Pretty.elifs bs)
  | [], _ => by simpa [Pretty.elifs] using Stream.nil
  | (t, b) :: bs, hw => by
    simp only [Node.BranchesWF] at hw
    obtain ⟨ht, hb, hbs⟩ := hw
    have hrest : Stream (Pretty.nodes b ++ Pretty.elifs bs) := by
      refine Stream.append (nodes_stream b hb) (elifs_stream bs hbs) (fun _ => ?_)
      cases bs with
      | nil => exact Or.inl (by simp [Pretty.elifs])
      | cons b' bs' => obtain ⟨t', b'⟩ := b'; right; simp [StartsTag, Pretty.elifs, Pretty.tag]
    have := Stream.block (lexOK_append (lexOK_kw "elif") (lexOK_expr ht)) (by simpa using blockHead_kw "elif" _) hrest
    simpa [Pretty.elifs, List.append_assoc] using this

theorem elsePart_stream : (els : List Node) → Node.BodyWF els → ∀ {c : List TokKind}, Stream c → StartsTag c →
    Stream ((if els.isEmpty then [] else Pretty.tag [Pretty.nm "else"] ++ Pretty.nodes els) ++ c) ∧
    StartsTag ((if els.isEmpty then [] else Pretty.tag [Pretty.nm "else"] ++ Pretty.nodes els) ++ c)
  | [], _, c, hc, ht => by simpa using ⟨hc, ht⟩
  | e :: es, hw, c, hc, ht => by
    have := Stream.block (lexOK_kw "else") (blockHead_kw "else" []) (Stream.thenTag (nodes_stream (e :: es) hw) hc ht)
    refine ⟨by simpa [List.append_assoc] using this, ?_⟩
    simp [StartsTag, Pretty.tag]
end

end LeanJinja2
