module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMgf
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# RSAES-OAEP on PPC64LE: MGF1 with the hash function of a table, twice

Untrusted: everything here is checked by Lean. `roundT_ct`: two runs of a
round of `mgfXorT` from states with `Base` and the same MGF1 registers
(`MgfRT`) leak alike: its blocks by the taint analysis, its calls through
the table by `tcall_two` and `init_ct`, `upd_ct` and `fin_ct`; the loads of
the table's words (`tword_two`) leak addresses both runs agree on, as both
tables are at the address the anchor's has and hold the same addresses of
`G`'s functions (`TabA`). `mgfXorT_ct`: the loop, whose condition both runs
agree on since each satisfies `MgfIT` for the same counter (`roundT_ok`), for
any public data that fix the stack pointer and `S` (`OkS`), or `Ok`'s.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo Two Pins two_post wp_li wp_addi wp_mov wp_nil eval_nonzero
  wp_addSp wp_ld)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaOaep.PPC64LE (Fns tcall tword)

/-- `B`, with the addresses of the statics of the entry. -/
def BT (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (a t : State) : Prop :=
  ∃ s, Pre s ∧ Pub a s ∧ Base S vf s t ∧ t.syms = s.syms

theorem BT.b {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
    {a t : State} (h : BT S vf Pre Pub a t) : B S vf Pre Pub a t :=
  let ⟨s, P, p, b, _⟩ := h; ⟨s, P, p, b⟩

/-- What each run's entry and the anchor have of the table that is our stack
argument `j`: in each run the table, of `G`, at the stack argument, at the
anchor's address and with the anchor's addresses of `G`'s functions. -/
structure TabA (G : Hash) (f : Fns) (j : Nat) (S : State → Addr) (Pre : State → Prop) (Pub : State → State → Prop) :
    Prop where
  tab : ∀ {s}, Pre s → TabS G f j S s (stackArg s j)
  arg : ∀ {a s}, Pub a s → stackArg s j = stackArg a j
  ai : ∀ {a s}, Pub a s → s.syms G.initN = a.syms G.initN
  au : ∀ {a s}, Pub a s → s.syms G.updN = a.syms G.updN
  af : ∀ {a s}, Pub a s → s.syms G.finN = a.syms G.finN

/-- In a round: `B` and MGF1's registers, for the counter `c`. -/
def MgfRT (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (Dg src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  BT S vf Pre Pub ac.1 t ∧ t.gpr .r24 = off (S ac.1) src ∧ t.gpr .r25 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r26 = off (S ac.1) dst ∧ t.gpr .r27 = BitVec.ofNat 64 dstLen ∧
    t.gpr .r28 = BitVec.ofNat 64 ac.2 ∧ t.gpr .r29 = BitVec.ofNat 64 (ac.2 * Dg) ∧ ac.2 * Dg < dstLen

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  {Dg src srcLen dst dstLen : Nat}

theorem MgfRT.keep {ac : State × Nat} {t t' : State} (h : MgfRT S vf Pre Pub Dg src srcLen dst dstLen ac t)
    (hb : BT S vf Pre Pub ac.1 t') (hg : ∀ r ∈ [Reg.r24, .r25, .r26, .r27, .r28, .r29], t'.gpr r = t.gpr r) :
    MgfRT S vf Pre Pub Dg src srcLen dst dstLen ac t' :=
  ⟨hb, (hg _ (by decide)).trans h.2.1, (hg _ (by decide)).trans h.2.2.1, (hg _ (by decide)).trans h.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.1, (hg _ (by decide)).trans h.2.2.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem mgfRT_pins (X : OkS S Pre Pub) {Φ : State × Nat → State → Prop}
    (h : ∀ ac t, Φ ac t → MgfRT S vf Pre Pub Dg src srcLen dst dstLen ac t) :
    Pins Φ [.r14, .r26, .r27, .r29] := fun ac t₁ t₂ h₁ h₂ => by
  obtain ⟨b₁, -, -, x26, x27, -, x29, -⟩ := h ac t₁ h₁
  obtain ⟨b₂, -, -, y26, y27, -, y29, -⟩ := h ac t₂ h₂
  refine ⟨(b₁.b.spS X).trans (b₂.b.spS X).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (b₁.b.r14S X).trans (b₂.b.r14S X).symm
  exacts [x26.trans y26.symm, x27.trans y27.symm, x29.trans y29.symm]

theorem mgfRT_base {Φ : State × Nat → State → Prop} (h : ∀ ac t, Φ ac t → MgfRT S vf Pre Pub Dg src srcLen dst dstLen ac t) :
    ∀ ac t, Φ ac t → B S vf Pre Pub ac.1 t := fun ac t hp => (h ac t hp).1.b

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG) {src srcLen dst dstLen : Nat}
  (hf : MFit src srcLen dst dstLen)

/-- Two runs with `B` for anchors agreeing on what an argument is. -/
theorem two_argsT {Φ : State × Nat → State → Prop} {t₁ t₂ : State} (h : Two Φ t₁ t₂)
    (hb : ∀ ac t, Φ ac t → B S vf Pre Pub ac.1 t) :
    ∃ ac s₁ s₂, Φ ac t₁ ∧ Φ ac t₂ ∧ Pre s₁ ∧ Pub ac.1 s₁ ∧ Base S vf s₁ t₁ ∧ Pre s₂ ∧ Pub ac.1 s₂ ∧
      Base S vf s₂ t₂ := by
  obtain ⟨ac, h₁, h₂⟩ := h
  obtain ⟨s₁, P₁, p₁, b₁⟩ := hb ac t₁ h₁
  obtain ⟨s₂, P₂, p₂, b₂⟩ := hb ac t₂ h₂
  exact ⟨ac, s₁, s₂, h₁, h₂, P₁, p₁, b₁, P₂, p₂, b₂⟩

/-! ## The table's words and calls, in two runs -/

section Tab
variable {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub)

include X A in
/-- The load of the table's word `k` into `d`, which is `v` of the anchor in
every run. -/
theorem tword_two {Φ : State × Nat → State → Prop} (hb : ∀ ac t, Φ ac t → BT S vf Pre Pub ac.1 t) {d : Reg}
    (hd : d = .r9 ∨ d = .r12) {k : Nat} (hk : k < 5) {v : State → BitVec 64}
    (hv : ∀ {a s}, Pre s → Pub a s → s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = v a) :
    RelCT isa (Two Φ) (.block (tword d j k))
      (Two fun ac u => ∃ t, Φ ac t ∧ Only [d] t u ∧ u.syms = t.syms ∧ u.gpr d = v ac.1) := by
  have hd0 : d ≠ .r0 := by rcases hd with rfl | rfl <;> decide
  have hrs : ∀ r ∈ [d], r ∉ .r14 :: fx ++ hiRegs := by
    intro r hr; rw [List.mem_singleton.mp hr]; rcases hd with rfl | rfl <;> decide
  let Ψ₁ := fun (ac : State × Nat) u => ∃ t, Φ ac t ∧ Only [d] t u ∧ u.syms = t.syms ∧ u.gpr d = stackArg ac.1 j
  show RelCT isa _ (.block ([.addSp d 0, .load .d d d (arg j)] ++ [.load .d d d (8 * k)])) _
  refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ₁) (twA_taint j hd fun ac t₁ t₂ h₁ h₂ =>
      ⟨((hb ac t₁ h₁).b.spS X).trans ((hb ac t₂ h₂).b.spS X).symm, fun _ h => nomatch h⟩) fun ac t h => ?_)
    (two_post (twB_taint (8 * k) hd fun ac u₁ u₂ ⟨t₁, h₁, o₁, _, e₁⟩ ⟨t₂, h₂, o₂, _, e₂⟩ =>
      ⟨by rw [o₁.sp, o₂.sp]; exact ((hb ac t₁ h₁).b.spS X).trans ((hb ac t₂ h₂).b.spS X).symm, fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]⟩) fun ac u ⟨t, h, o, sy, e⟩ => ?_))
  · obtain ⟨s, P, p, b, _⟩ := hb ac t h
    have T := A.tab P
    refine WP.of_syms (wp_addSp fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j)
      (by rw [e₁, b.sp, BitVec.add_zero, stackArgAddr_fb])
      (by rw [o₁.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o₁.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂, by
          rw [e₂, o₁.mem, b.readW_apart T.argK T.argS, ← A.arg p]; rfl⟩) hd0 T.jo)
  · obtain ⟨s, P, p, b, sy₀⟩ := hb ac t h
    have T := A.tab P
    have bu := b.only (X.fits P) o hrs
    refine WP.of_syms (wp_ld (a := stackArg s j + BitVec.ofNat 64 (8 * k)) (by rw [e, A.arg p])
      (by rw [o.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂.trans sy, by
          rw [e₂, o.mem, b.readW_apart (T.tK k hk) (T.tS k hk), hv P p]⟩) hd0 (by omega))

include X A in
/-- The call of the table's function `k`, among `ts`, which reaches `n` in
every run, at the anchor's address of `n`, as the call of `n` from the
states the load of its address leaves. -/
theorem tcall_two {Φ : State × Nat → State → Prop} (hb : ∀ ac t, Φ ac t → BT S vf Pre Pub ac.1 t) {k : Nat}
    (hk : k < 3) {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hn : ∀ {a s}, Pre s → Pub a s → ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c) ∧
      s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = s.syms n ∧ s.syms n = a.syms n)
    (hcall : RelCT isa (Two fun ac u => ∃ t, Φ ac t ∧ Only [.r12] t u ∧ u.syms = t.syms) (.call n c)
      fun _ _ => True) :
    RelCT isa (Two Φ) (tcall j k ts) fun _ _ => True := by
  refine RelCT.seq (tword_two X A hb (d := .r12) (.inr rfl) (k := k) (by omega) (v := fun a => a.syms n)
    fun P p => (hn P p).2.1.trans (hn P p).2.2) ?_
  cases ts with
  | nil =>
    exact RelCT.of_false fun s₁ s₂ ⟨ac, ⟨t, h, _⟩, _⟩ => by
      obtain ⟨s, P, p, _⟩ := hb ac t h
      simpa using (hn P p).1
  | cons q ts =>
    refine RelCT.icalls_of_call (hcall.mono (fun _ _ ⟨ac, ⟨t₁, h₁, o₁, y₁, _⟩, ⟨t₂, h₂, o₂, y₂, _⟩⟩ =>
      ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩) fun _ _ h => h) ?_
    rintro u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, y₁, e₁⟩, ⟨t₂, h₂, o₂, y₂, e₂⟩⟩
    obtain ⟨s₁, P₁, p₁, -, z₁⟩ := hb ac t₁ h₁
    obtain ⟨s₂, P₂, p₂, -, z₂⟩ := hb ac t₂ h₂
    have tg : ∀ {u t s : State}, u.syms = t.syms → t.syms = s.syms → Pre s → Pub ac.1 s → u.gpr .r12 = ac.1.syms n →
        icallTarget isa u (ac.1.syms n) (q :: ts) = some (n, c) := fun {u t s} y z P p _ => by
      show (q :: ts).find? (fun q => u.syms q.1 == ac.1.syms n) = _
      rw [y, z, ← (hn P p).2.2]; exact (hn P p).1
    exact ⟨ac.1.syms n, by show some (u₁.gpr .r12) = _; rw [e₁], by show some (u₂.gpr .r12) = _; rw [e₂],
      tg y₁ z₁ P₁ p₁ e₁, tg y₂ z₂ P₂ p₂ e₂, rfl⟩

end Tab

include X hG hf in
/-- The rest of `xorOutT` keeps `BT`. -/
theorem xorOutT_base {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub) {ac : State × Nat} {t : State}
    (h : MgfRT S vf Pre Pub G.D src srcLen dst dstLen ac t) :
    WP isa (xorOutT j) t (BT S vf Pre Pub ac.1) := by
  have F := hfits hG
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hD0 := hG.hD0
  have hD64 := hG.hD64
  have hfd := hf.fd
  obtain ⟨⟨s, P, p, b, sy⟩, -, -, h26, h27, -, h29, hc⟩ := h
  have hdc := Nat.min_le_left G.D (dstLen - ac.2 * G.D)
  have hn0 : 0 < min G.D (dstLen - ac.2 * G.D) := by omega_arith
  refine WP.of_syms (WP.seq (WP.mono (xorHeadT_ok (A.tab P) b (G := G) (S := S s) (dst := dst) (dstLen := dstLen)
    (done := ac.2 * G.D) (by omega_arith) b.r14 (by rw [h26, (X.S p)]) h27 h29 hc (by omega_arith))
    fun t₁ ⟨k₁, x11, x12, x9⟩ => ?_))
  have b₁ := b.only (X.fits P) k₁
  refine WP.mono (xorLoop_ok (p := off (S s) (dst + ac.2 * G.D)) (q := off (S s) oDig) hn0 (by omega_arith) x11 x12 x9
    (fun j hj => by
      rw [off_add, k₁.rd, k₁.wr, b.wr, b.rd]; exact sc_inR (X.fits P) (by omega_arith) _)
    (sc_w (X.fits P) (by rw [k₁.wr, b.wr]) (by omega_arith))
    (fun j hj i hi => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith))
    (fun i hi j hj hij => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)))
    fun t₂ ⟨k₂, x₂⟩ sy₂ => ⟨s, P, p, b₁.wb (X.fits P) k₂ (by rw [xorAt_length]; omega_arith) x₂, sy₂.trans sy⟩

include X cG hf in
theorem roundT_ct {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub) :
    RelCT isa (Two (MgfRT S vf Pre Pub G.D src srcLen dst dstLen)) (roundT f j) fun _ _ => True := by
  have F := hfits hG
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hfs := hf.fs
  have hfd := hf.fd
  have p0 : ∀ {Φ : State × Nat → State → Prop}, (∀ ac t, Φ ac t → MgfRT S vf Pre Pub G.D src srcLen dst dstLen ac t) →
      Pins Φ [] := fun h ac t₁ t₂ h₁ h₂ => ⟨((mgfRT_pins X h) ac t₁ t₂ h₁ h₂).1, fun _ h => nomatch h⟩
  let M := MgfRT S vf Pre Pub G.D src srcLen dst dstLen
  have pres : ∀ {t t' : State}, (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      ∀ r ∈ [Reg.r24, .r25, .r26, .r27, .r28, .r29], t'.gpr r = t.gpr r :=
    fun h r hr => h r (by revert r; decide)
  have o12 : ∀ {t u : State}, Only [.r12] t u → ∀ r ∈ [Reg.r24, .r25, .r26, .r27, .r28, .r29], u.gpr r = t.gpr r :=
    fun o r hr => o.gpr r (by revert r; decide)
  -- A state after the load of a table's function's address keeps `M`'s `Base`.
  have bt12 : ∀ {ac t u}, M ac t → Only [.r12] t u → u.syms = t.syms → BT S vf Pre Pub ac.1 u :=
    fun {ac t u} h o y => let ⟨s, P, p, b, sy⟩ := h.1; ⟨s, P, p, b.only (X.fits P) o, y.trans sy⟩
  -- `init`.
  refine two_seq (Ψ := fun ac t => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt) (st_taint (p0 fun _ _ h => h))
    (fun ac t h => WP.of_syms (wp_addi fun t' o e => wp_nil fun sy =>
      let ⟨s, P, p, b, y⟩ := h.1
      ⟨h.keep ⟨s, P, p, b.only (X.fits P) o, sy.trans y⟩ (fun r hr => o.gpr r (by revert r; decide)),
        by rw [e, b.r14, (X.S p)]⟩)) ?_
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 0) (by decide)
    (fun P p => ⟨(A.tab P).ok.i, by rw [Nat.mul_zero, BitVec.add_zero]; exact (A.tab P).mem.1, A.ai p⟩)
    (init_ct (S := S) (vf := vf) cG fun u₁ u₂ hp => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ := hp
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := (bt12 h₁.1 o₁ y₁)
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := (bt12 h₂.1 o₂ y₂)
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [o₁.get .r3, h₁.2, (X.S p₁)], X.fits P₂, b₂,
      by rw [o₂.get .r3, h₂.2, (X.S p₂)], by rw [o₁.get .r3, o₂.get .r3, h₁.2, h₂.2],
      (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
  · obtain ⟨hm, h3⟩ := h
    obtain ⟨s, P, p, b, sy⟩ := hm.1
    exact WP.mono (initT_ok (X.fits P) (A.tab P) hG b sy (by rw [h3, (X.S p)])) fun t' ⟨⟨b', g', _⟩, sy'⟩ =>
      hm.keep ⟨s, P, p, b', sy'⟩ (pres g')
  -- `update` with `src`.
  let U₁ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt ∧
    t.gpr .r4 = 0 ∧ t.gpr .r5 = off (S ac.1) src ∧ t.gpr .r6 = BitVec.ofNat 64 srcLen ∧
    t.gpr .r7 = off (S ac.1) oW
  refine two_seq (Ψ := U₁) (r2_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ =>
      wp_mov fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ => wp_nil fun sy => ?_)
    have k : Only [.r3, .r4, .r5, .r6, .r7] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    obtain ⟨s, P, p, b, y⟩ := h.1
    refine ⟨h.keep ⟨s, P, p, b.only (X.fits P) k, sy.trans y⟩ (fun r hr => k.gpr r (by revert r; decide)),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.get .r3, o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, (X.S p)]
    · rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, e₂]; rfl
    · rw [o₅.get .r5, o₄.get .r5, e₃, o₂.get .r24, o₁.get .r24, h.2.1]
    · rw [o₅.get .r6, e₄, o₃.get .r25, o₂.get .r25, o₁.get .r25, h.2.2.1]
    · rw [e₅, o₄.get .r14, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, (X.S p)]
  have uargs : ∀ {ac : State × Nat} {t : State}, U₁ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) src) srcLen ∧ Pub ac.1 s ∧ t.syms = s.syms := fun {ac t} h => by
    obtain ⟨hm, h3, -, h5, h6, h7⟩ := h
    obtain ⟨s, P, p, b, y⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h3, (X.S p)], by rw [h5, (X.S p)], by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)],
      by rw [h7, (X.S p)], Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega_arith)),
      sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith), sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
      cR_dis (X.fits P) (by omega_arith)⟩, p, y⟩
  have uargs12 : ∀ {U : State × Nat → State → Prop}, (∀ {ac t}, U ac t → ∃ s d l, Pre s ∧ UpdArgs S vf G s t d l ∧
      Pub ac.1 s ∧ t.syms = s.syms) → ∀ {ac : State × Nat} {t u : State}, U ac t → Only [.r12] t u →
      ∃ s d l, UpdArgs S vf G s u d l ∧ Pub ac.1 s := fun {U} hU {ac t u} h o => by
    obtain ⟨s, d, l, P, A', p, -⟩ := hU h
    exact ⟨s, d, l, ⟨A'.P, A'.b.only A'.P o, by rw [o.get .r3]; exact A'.h3, by rw [o.get .r5]; exact A'.h5,
      by rw [o.get .r6]; exact A'.h6, by rw [o.get .r7]; exact A'.h7, by rw [o.rd, o.wr]; exact A'.hdc, A'.hd₁, A'.hd₂,
      A'.hd₃⟩, p⟩
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 1) (by decide)
    (fun P p => ⟨(A.tab P).ok.u, by rw [Nat.mul_one]; exact (A.tab P).mem.2.1, A.au p⟩)
    (upd_ct (S := S) (vf := vf) cG fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, _⟩, ⟨t₂, h₂, o₂, _⟩⟩ => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨s₁, d₁, l₁, A₁, p₁⟩ := uargs12 (U := U₁) (fun h => let ⟨s, P, A', p, y⟩ := uargs h; ⟨s, _, _, P, A', p, y⟩) h₁ o₁
    obtain ⟨s₂, d₂, l₂, A₂, p₂⟩ := uargs12 (U := U₁) (fun h => let ⟨s, P, A', p, y⟩ := uargs h; ⟨s, _, _, P, A', p, y⟩) h₂ o₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [o₁.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
      o₂.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm]
  · obtain ⟨s, P, A', p, y⟩ := uargs h
    exact WP.mono (updT_ok A'.P (A.tab P) hG A'.b y A'.h3 A'.h5 A'.h6 A'.h7 A'.hdc A'.hd₁ A'.hd₂ A'.hd₃)
      fun t' ⟨⟨b', g', _⟩, y'⟩ => h.1.keep ⟨s, P, p, b', y'⟩ (pres g')
  -- The counter, and `update` with it.
  let U₂ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt ∧
    t.gpr .r4 = BitVec.ofNat 64 srcLen ∧ t.gpr .r5 = off (S ac.1) oCtr ∧ t.gpr .r6 = BitVec.ofNat 64 4 ∧
    t.gpr .r7 = off (S ac.1) oW
  have hD0 := hG.hD0
  refine two_seq (Ψ := U₂) (ctr_taint (pins_mono (mgfRT_pins X fun _ _ h => h))) (fun ac t h => ?_) ?_
  · obtain ⟨s, P, p, b, y⟩ := h.1
    have hc : ac.2 < 2 ^ 32 := by
      have := h.2.2.2.2.2.2.2; have := Nat.le_mul_of_pos_right ac.2 hD0; omega_arith
    exact WP.mono_syms (ctr_ok (X.fits P) b h.2.2.2.2.2.1 hc) fun t' ⟨b', g', _, x3, x4, x5, x6, x7⟩ y' =>
      ⟨h.keep ⟨s, P, p, b', y'.trans y⟩ (pres g'), by rw [x3, (X.S p)], by rw [x4, h.2.2.1], by rw [x5, (X.S p)], x6,
        by rw [x7, (X.S p)]⟩
  have cargs : ∀ {ac : State × Nat} {t : State}, U₂ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) oCtr) 4 ∧ Pub ac.1 s ∧ t.syms = s.syms := fun {ac t} h => by
    obtain ⟨hm, h3, -, h5, h6, h7⟩ := h
    obtain ⟨s, P, p, b, y⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h3, (X.S p)], by rw [h5, (X.S p)], by rw [h6]; rfl, by rw [h7, (X.S p)],
      Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega_arith)),
      sdis (.inr (by omega_arith)) (by omega_arith) (by omega_arith), sdis (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
      cR_dis (X.fits P) (by omega_arith)⟩, p, y⟩
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 1) (by decide)
    (fun P p => ⟨(A.tab P).ok.u, by rw [Nat.mul_one]; exact (A.tab P).mem.2.1, A.au p⟩)
    (upd_ct (S := S) (vf := vf) cG fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, _⟩, ⟨t₂, h₂, o₂, _⟩⟩ => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨s₁, d₁, l₁, A₁, p₁⟩ := uargs12 (U := U₂) (fun h => let ⟨s, P, A', p, y⟩ := cargs h; ⟨s, _, _, P, A', p, y⟩) h₁ o₁
    obtain ⟨s₂, d₂, l₂, A₂, p₂⟩ := uargs12 (U := U₂) (fun h => let ⟨s, P, A', p, y⟩ := cargs h; ⟨s, _, _, P, A', p, y⟩) h₂ o₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [o₁.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
      o₂.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm]
  · obtain ⟨s, P, A', p, y⟩ := cargs h
    exact WP.mono (updT_ok A'.P (A.tab P) hG A'.b y A'.h3 A'.h5 A'.h6 A'.h7 A'.hdc A'.hd₁ A'.hd₂ A'.hd₃)
      fun t' ⟨⟨b', g', _⟩, y'⟩ => h.1.keep ⟨s, P, p, b', y'⟩ (pres g')
  -- `finalize`.
  let U₃ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .r3 = off (S ac.1) oSt ∧
    t.gpr .r4 = BitVec.ofNat 64 srcLen + BitVec.ofNat 64 4 ∧ t.gpr .r5 = off (S ac.1) oDig ∧
    t.gpr .r6 = off (S ac.1) oW
  refine two_seq (Ψ := U₃) (r4_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine WP.of_syms (wp_addi fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_addi fun t₃ o₃ e₃ =>
      wp_addi fun t₄ o₄ e₄ => wp_nil fun sy => ?_)
    have k : Only [.r3, .r4, .r5, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    obtain ⟨s, P, p, b, y⟩ := h.1
    refine ⟨h.keep ⟨s, P, p, b.only (X.fits P) k, sy.trans y⟩ (fun r hr => k.gpr r (by revert r; decide)),
      ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .r3, o₃.get .r3, o₂.get .r3, e₁, b.r14, (X.S p)]
    · rw [o₄.get .r4, o₃.get .r4, e₂, o₁.get .r25, h.2.2.1]
    · rw [o₄.get .r5, e₃, o₂.get .r14, o₁.get .r14, b.r14, (X.S p)]
    · rw [e₄, o₃.get .r14, o₂.get .r14, o₁.get .r14, b.r14, (X.S p)]
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 2) (by decide)
    (fun P p => ⟨(A.tab P).ok.f, by rw [show 8 * 2 = 16 from rfl]; exact (A.tab P).mem.2.2, A.af p⟩)
    (fin_ct (S := S) (vf := vf) cG fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_)) (fun ac t h => ?_) ?_
  · have ⟨_, x3, x4, x5, x6⟩ := h₁
    have ⟨_, y3, y4, y5, y6⟩ := h₂
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := bt12 h₁.1 o₁ y₁
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := bt12 h₂.1 o₂ y₂
    have g : ∀ {t u : State}, Only [.r12] t u → ∀ r ∈ [Reg.r3, .r4, .r5, .r6], u.gpr r = t.gpr r :=
      fun o r hr => o.gpr r (by revert r; decide)
    refine ⟨s₁, s₂, ⟨X.fits P₁, b₁, by rw [g o₁ _ (by decide), x3, (X.S p₁)], by rw [g o₁ _ (by decide), x5, (X.S p₁)],
        by rw [g o₁ _ (by decide), x6, (X.S p₁)]⟩,
      ⟨X.fits P₂, b₂, by rw [g o₂ _ (by decide), y3, (X.S p₂)], by rw [g o₂ _ (by decide), y5, (X.S p₂)],
        by rw [g o₂ _ (by decide), y6, (X.S p₂)]⟩, fun r hr => ?_, (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
    rw [g o₁ r hr, g o₂ r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [x3.trans y3.symm, x4.trans y4.symm, x5.trans y5.symm, x6.trans y6.symm]
  · obtain ⟨hm, h3, -, h5, h6⟩ := h
    obtain ⟨s, P, p, b, y⟩ := hm.1
    exact WP.mono (finT_ok (X.fits P) (A.tab P) hG b y (by rw [h3, (X.S p)]) (by rw [h5, (X.S p)])
      (by rw [h6, (X.S p)])) fun t' ⟨⟨b', g', _⟩, y'⟩ => hm.keep ⟨s, P, p, b', y'⟩ (pres g')
  -- Into `dst`, and the next counter.
  have bD : ∀ {a s}, Pre s → Pub a s → s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * 4)) 64 =
      BitVec.ofNat 64 G.D := fun P _ => (A.tab P).d
  have xo : RelCT isa (Two M) (xorOutT j) fun _ _ => True := by
    show RelCT isa _ (.seq (.block (tword .r9 j 4 ++ xorRest)) (.loop (.block xorBody) (.nonzero .d .r9))) _
    refine RelCT.seq_block_append (RelCT.seq (tword_two X A (Φ := M) (fun ac t h => h.1) (d := .r9) (.inl rfl)
      (k := 4) (by decide) (v := fun _ => BitVec.ofNat 64 G.D) bD) (xorRest_taint fun ac u₁ u₂ hu₁ hu₂ => ?_))
    obtain ⟨t₁, h₁, o₁, _, e₁⟩ := hu₁
    obtain ⟨t₂, h₂, o₂, _, e₂⟩ := hu₂
    obtain ⟨hsp, hr⟩ := (mgfRT_pins X (fun _ _ h => h)) ac t₁ t₂ h₁ h₂
    refine ⟨by rw [o₁.sp, o₂.sp]; exact hsp, fun r hr' => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · rw [e₁, e₂]
    all_goals rw [o₁.get _ (by decide), o₂.get _ (by decide)]; exact hr _ (by decide)
  have nc : RelCT isa (Two fun (ac : State × Nat) t => BT S vf Pre Pub ac.1 t) (.block (nextCtrT j))
      fun _ _ => True := by
    show RelCT isa _ (.block (tword .r12 j 4 ++ nextRest)) _
    refine RelCT.block_append (RelCT.seq (tword_two X A (fun _ _ h => h) (d := .r12) (.inr rfl) (k := 4) (by decide)
      (v := fun _ => BitVec.ofNat 64 G.D) bD) (nextRest_taint fun ac u₁ u₂ hu₁ hu₂ => ?_))
    obtain ⟨t₁, h₁, o₁, _⟩ := hu₁
    obtain ⟨t₂, h₂, o₂, _⟩ := hu₂
    exact ⟨by rw [o₁.sp, o₂.sp]; exact (h₁.b.spS X).trans (h₂.b.spS X).symm, fun _ h => nomatch h⟩
  exact two_seq (Ψ := fun (ac : State × Nat) t => BT S vf Pre Pub ac.1 t) xo (fun ac t h => xorOutT_base X hG hf A h) nc

/-- MGF1's arguments in `r24`–`r27`, from the anchor. -/
def MgfAT (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  ∃ s, Pre s ∧ Pub a s ∧ Base S vf s t ∧ t.syms = s.syms ∧ t.gpr .r24 = off (S a) src ∧
    t.gpr .r25 = BitVec.ofNat 64 srcLen ∧ t.gpr .r26 = off (S a) dst ∧
    t.gpr .r27 = BitVec.ofNat 64 dstLen

variable {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)

/-- After `c` rounds, in a run: `MgfIT` for some view, and the counter below
the end. -/
def MgfLT (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (G : Hash) (Gs : Spec.Mgf1.Hash) (src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  ∃ s V, Pre s ∧ Pub ac.1 s ∧
    MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D ac.2 t ∧ ac.2 * G.D < dstLen

include X in
theorem mgfLT_r {ac : State × Nat} {t : State} (h : MgfLT S vf Pre Pub G Gs src srcLen dst dstLen ac t) :
    MgfRT S vf Pre Pub G.D src srcLen dst dstLen ac t := by
  obtain ⟨s, V, P, p, I, hc⟩ := h
  exact ⟨⟨s, P, p, I.base, I.sy⟩, by rw [I.r24, (X.S p)], I.r25, by rw [I.r26, (X.S p)], I.r27, I.r28, I.r29, hc⟩

include X cG hf hGh hGl hGv in
theorem mgfXorT_ctS {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub) :
    RelCT isa (Two (MgfAT S vf Pre Pub src srcLen dst dstLen)) (mgfXorT f j) fun _ _ => True := by
  have hD0 := hG.hD0
  have hpos := hf.pos
  let L := MgfLT S vf Pre Pub G Gs src srcLen dst dstLen
  let Ln := fun (n : Nat) (ac : State × Nat) (t : State) => L ac t ∧ n = dstLen - ac.2 * G.D
  have step : ∀ n, RelCT isa (Two (Ln n)) (roundT f j) fun s₁ s₂ =>
      isa.eval (.nonzero .d .r12) s₁ = isa.eval (.nonzero .d .r12) s₂ ∧
      (isa.eval (.nonzero .d .r12) s₁ = some false → True) ∧
      (isa.eval (.nonzero .d .r12) s₁ = some true → ∃ m < n, Two (Ln m) s₁ s₂) := fun n => by
    have h := two_post (Φ := Ln n) (Ψ := fun ac t => (t.gpr .r12 != 0) = decide ((ac.2 + 1) * G.D < dstLen) ∧
        ∃ s V, Pre s ∧ Pub ac.1 s ∧
          MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D (ac.2 + 1) t ∧
          n = dstLen - ac.2 * G.D)
      ((roundT_ct X hG cG hf A).mono (fun _ _ ⟨ac, h₁, h₂⟩ => ⟨ac, mgfLT_r X h₁.1, mgfLT_r X h₂.1⟩) fun _ _ h => h)
      (fun ac t ⟨⟨s, V, P, p, I, hc⟩, hn⟩ => WP.mono (roundT_ok (X.fits P) hG (A.tab P) hGh hGl hGv hf I hc)
        fun t' ⟨hcf, I'⟩ => ⟨hcf, s, V, P, p, I', hn⟩)
    refine h.mono (fun _ _ h => h) fun s₁ s₂ ⟨ac, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ => ?_
    have hs1 : (ac.2 + 1) * G.D = ac.2 * G.D + G.D := Nat.succ_mul _ _
    refine ⟨by rw [eval_nonzero, eval_nonzero, c₁, c₂], fun _ => trivial, fun ht => ?_⟩
    rw [eval_nonzero, c₁] at ht
    have hlt : (ac.2 + 1) * G.D < dstLen := by simpa using ht
    obtain ⟨s, V, P, p, I, hn⟩ := h₁
    obtain ⟨s', V', P', p', I', -⟩ := h₂
    exact ⟨dstLen - (ac.2 + 1) * G.D, by omega_arith, (ac.1, ac.2 + 1), ⟨⟨s, V, P, p, I, hlt⟩, rfl⟩,
      ⟨⟨s', V', P', p', I', hlt⟩, rfl⟩⟩
  refine RelCT.seq (two_post (Ψ := fun a t => L (a, 0) t) (mgfHead_taint fun a t₁ t₂ h₁ h₂ => ?_)
    (fun a t h => ?_)) ((RelCT.loop (fun n => Two (Ln n)) step (dstLen - 0 * G.D)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h)
  · obtain ⟨_, -, p₁, b₁, -, -⟩ := h₁
    obtain ⟨_, -, p₂, b₂, -, -⟩ := h₂
    exact ⟨(Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm, fun _ h => nomatch h⟩
  · obtain ⟨s, P, p, b, sy, h24, h25, h26, h27⟩ := h
    refine WP.of_syms (wp_li (by decide) fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_nil fun sy₂ => ?_)
    have k₂ : Only [.r28, .r29] t t₂ := (o₁.trans o₂).mono
    exact ⟨s, view t.mem (S s), P, p, ⟨b.only (X.fits P) k₂, by rw [k₂.get .r24, h24, (X.S p)], by rw [k₂.get .r25, h25],
      by rw [k₂.get .r26, h26, (X.S p)], by rw [k₂.get .r27, h27], by rw [o₂.get .r28, e₁], by rw [e₂, Nat.zero_mul],
      fun o _ => by rw [mixV, ifn (by omega_arith), k₂.mem], sy₂.trans sy⟩, by omega_arith⟩

end

/-- `mgfXorT_ctS` for `Ok`. -/
theorem mgfXorT_ct {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop}
    {Pub : State → State → Prop} (X : Ok S vf Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG)
    {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns} {j : Nat}
    (A : TabA G f j S Pre Pub) :
    RelCT isa (Two (MgfAT S vf Pre Pub src srcLen dst dstLen)) (mgfXorT f j) fun _ _ => True :=
  mgfXorT_ctS X.s hG cG hf hGh hGl hGv A

end VG.Proof.RsaOaep.PPC64LE
