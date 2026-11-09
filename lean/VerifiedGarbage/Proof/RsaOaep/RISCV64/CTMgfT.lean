module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBase
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTBlocks
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# RSAES-OAEP on RISC-V: MGF1 with the hash function of a table, twice

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/CTMgfT.lean`): `roundT_ct`, two runs of a round of
`mgfXorT` from states with `Base` and the same MGF1 registers (`MgfRT`) leak
alike: its blocks by the taint analysis, its calls through the table by
`tcall_two` and `init_ct`, `upd_ct` and `fin_ct`; the loads of the table's
words (`tword_two`) leak addresses both runs agree on, as both tables are at
the address the anchor's has and hold the same addresses of `G`'s functions
(`TabA`). `mgfXorT_ct`: the loop, whose condition both runs agree on since
each satisfies `MgfIT` for the same counter (`roundT_ok`), for any public
data that fix the stack pointer and `S` (`OkS`), or `Ok`'s.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo Two Pins two_post wp_li wp_addi wp_mov wp_nil eval_nonzero
  wp_addSp wp_ld)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

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

/-- In a round: `BT` and MGF1's registers, for the counter `c`. -/
def MgfRT (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (Dg src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  BT S vf Pre Pub ac.1 t ∧ t.gpr .s6 = off (S ac.1) src ∧ t.gpr .s7 = BitVec.ofNat 64 srcLen ∧
    t.gpr .s8 = off (S ac.1) dst ∧ t.gpr .s9 = BitVec.ofNat 64 dstLen ∧
    t.gpr .s10 = BitVec.ofNat 64 ac.2 ∧ t.gpr .s11 = BitVec.ofNat 64 (ac.2 * Dg) ∧ ac.2 * Dg < dstLen

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  {Dg src srcLen dst dstLen : Nat}

theorem MgfRT.keep {ac : State × Nat} {t t' : State} (h : MgfRT S vf Pre Pub Dg src srcLen dst dstLen ac t)
    (hb : BT S vf Pre Pub ac.1 t') (hg : ∀ r ∈ [Reg.s6, .s7, .s8, .s9, .s10, .s11], t'.gpr r = t.gpr r) :
    MgfRT S vf Pre Pub Dg src srcLen dst dstLen ac t' :=
  ⟨hb, (hg _ (by decide)).trans h.2.1, (hg _ (by decide)).trans h.2.2.1, (hg _ (by decide)).trans h.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.1, (hg _ (by decide)).trans h.2.2.2.2.2.1,
    (hg _ (by decide)).trans h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem mgfRT_pins (X : OkS S Pre Pub) {Φ : State × Nat → State → Prop}
    (h : ∀ ac t, Φ ac t → MgfRT S vf Pre Pub Dg src srcLen dst dstLen ac t) :
    Pins Φ [.s0, .s8, .s9, .s11] := fun ac t₁ t₂ h₁ h₂ => by
  obtain ⟨b₁, -, -, x8, x9, -, x11, -⟩ := h ac t₁ h₁
  obtain ⟨b₂, -, -, y8, y9, -, y11, -⟩ := h ac t₂ h₂
  refine ⟨(b₁.b.spS X).trans (b₂.b.spS X).symm, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (b₁.b.s0S X).trans (b₂.b.s0S X).symm
  exacts [x8.trans y8.symm, x9.trans y9.symm, x11.trans y11.symm]

theorem pins_monoT {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : Pins Φ rs' := fun a t₁ t₂ h₁ h₂ =>
  ⟨(h a t₁ t₂ h₁ h₂).1, fun r hr => (h a t₁ t₂ h₁ h₂).2 r (hs r hr)⟩

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG) (hF : G.F ≤ 208) {src srcLen dst dstLen : Nat}
  (hf : MFit src srcLen dst dstLen)

/-! ## The table's words and calls, in two runs -/

section Tab
variable {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub)

include X A in
/-- The load of the table's word `k` into `d`, which is `v` of the anchor in
every run. -/
theorem tword_two {Φ : State × Nat → State → Prop} (hb : ∀ ac t, Φ ac t → BT S vf Pre Pub ac.1 t) {d : Reg}
    (hd : d = .a6 ∨ d = .t1 ∨ d = .a0) {k : Nat} (hk : k < 5) {v : State → BitVec 64}
    (hv : ∀ {a s}, Pre s → Pub a s → s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = v a) :
    RelCT isa (Two Φ) (.block (tword d j k))
      (Two fun ac u => ∃ t, Φ ac t ∧ Only [d] t u ∧ u.syms = t.syms ∧ u.gpr d = v ac.1) := by
  have hrs : ∀ r ∈ [d], r ∉ fixed := by
    intro r hr; rw [List.mem_singleton.mp hr]; rcases hd with rfl | rfl | rfl <;> decide
  let Ψ₁ := fun (ac : State × Nat) u => ∃ t, Φ ac t ∧ Only [d] t u ∧ u.syms = t.syms ∧ u.gpr d = stackArg ac.1 j
  show RelCT isa _ (.block ([.addSp d (frameBytes + 8 * j), .load .d d d 0] ++ [.load .d d d (8 * k)])) _
  refine RelCT.block_append (RelCT.seq (two_post (Ψ := Ψ₁) (twA_taint j hd fun ac t₁ t₂ h₁ h₂ =>
      ⟨((hb ac t₁ h₁).b.spS X).trans ((hb ac t₂ h₂).b.spS X).symm, fun _ h => nomatch h⟩) fun ac t h => ?_)
    (two_post (twB_taint (8 * k) hd fun ac u₁ u₂ ⟨t₁, h₁, o₁, _, e₁⟩ ⟨t₂, h₂, o₂, _, e₂⟩ =>
      ⟨by rw [o₁.sp, o₂.sp]; exact ((hb ac t₁ h₁).b.spS X).trans ((hb ac t₂ h₂).b.spS X).symm, fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]⟩) fun ac u ⟨t, h, o, sy, e⟩ => ?_))
  · obtain ⟨s, P, p, b, _⟩ := hb ac t h
    have T := A.tab P
    refine WP.of_syms (wp_addSp (h := T.jo) fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j)
      (by rw [e₁, b.sp, ← stackArgAddr_fb]; simp) T.argA
      (by rw [o₁.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.argR; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o₁.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂, by
          rw [e₂, o₁.mem, b.readW_apart T.argK T.argS, ← A.arg p]; rfl⟩))
  · obtain ⟨s, P, p, b, sy₀⟩ := hb ac t h
    have T := A.tab P
    refine WP.of_syms (wp_ld (a := stackArg s j + BitVec.ofNat 64 (8 * k)) (by rw [e, A.arg p]) (T.wA hk)
      (by rw [o.rd, b.rd]; exact let ⟨R, hR, hc⟩ := T.tR k hk; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₂ o₂ e₂ => wp_nil fun sy₂ => ⟨t, h, (o.trans o₂).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, sy₂.trans sy, by
          rw [e₂, o.mem, b.readW_apart (T.tK k hk) (T.tS k hk), hv P p]⟩) (by omega))

include X A in
/-- The call of the table's function `k`, among `ts`, which reaches `n` in
every run, at the anchor's address of `n`, as the call of `n` from the
states the load of its address leaves. -/
theorem tcall_two {Φ : State × Nat → State → Prop} (hb : ∀ ac t, Φ ac t → BT S vf Pre Pub ac.1 t) {k : Nat}
    (hk : k < 3) {ts : List (String × Prog isa)} {n : String} {c : Prog isa}
    (hn : ∀ {a s}, Pre s → Pub a s → ts.find? (fun q => s.syms q.1 == s.syms n) = some (n, c) ∧
      s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * k)) 64 = s.syms n ∧ s.syms n = a.syms n)
    (hcall : RelCT isa (Two fun ac u => ∃ t, Φ ac t ∧ Only [.t1] t u ∧ u.syms = t.syms) (.call n c)
      fun _ _ => True) :
    RelCT isa (Two Φ) (tcall j k ts) fun _ _ => True := by
  refine RelCT.seq (tword_two X A hb (d := .t1) (.inr (.inl rfl)) (k := k) (by omega) (v := fun a => a.syms n)
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
    have tg : ∀ {u t s : State}, u.syms = t.syms → t.syms = s.syms → Pre s → Pub ac.1 s → u.gpr .t1 = ac.1.syms n →
        icallTarget isa u (ac.1.syms n) (q :: ts) = some (n, c) := fun {u t s} y z P p _ => by
      show (q :: ts).find? (fun q => u.syms q.1 == ac.1.syms n) = _
      rw [y, z, ← (hn P p).2.2]; exact (hn P p).1
    exact ⟨ac.1.syms n, by show some (u₁.gpr .t1) = _; rw [e₁], by show some (u₂.gpr .t1) = _; rw [e₂],
      tg y₁ z₁ P₁ p₁ e₁, tg y₂ z₂ P₂ p₂ e₂, rfl⟩

end Tab

include X hG hf in
/-- `xorOutT` keeps `BT`. -/
theorem xorOutT_base {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub) {ac : State × Nat} {t : State}
    (h : MgfRT S vf Pre Pub G.D src srcLen dst dstLen ac t) :
    WP isa (xorOutT j) t (BT S vf Pre Pub ac.1) := by
  have F := hfits hG
  obtain ⟨_, _, _, _, _⟩ := offs
  have hD0 := hG.hD0
  have hD64 := hG.hD64
  have hfd := hf.fd
  obtain ⟨⟨s, P, p, b, sy⟩, -, -, h8, h9, -, h11, hc⟩ := h
  have hdc := Nat.min_le_left G.D (dstLen - ac.2 * G.D)
  have hn0 : 0 < min G.D (dstLen - ac.2 * G.D) := by omega
  refine WP.of_syms (WP.seq (WP.mono (xorHeadT_ok (A.tab P) b (G := G) (S := S s) (dst := dst) (dstLen := dstLen)
    (done := ac.2 * G.D) (by omega) b.s0 (by rw [h8, (X.S p)]) h9 h11 hc (by omega))
    fun t₁ ⟨k₁, x4, x5, x6⟩ => ?_))
  have b₁ := b.only (X.fits P) k₁
  refine WP.mono (xorLoop_ok (p := off (S s) (dst + ac.2 * G.D)) (q := off (S s) oDig) hn0 (by omega) x4 x5 x6
    (fun j hj => by
      rw [off_add, k₁.rd, k₁.wr, b.wr, b.rd]; exact sc_inR (X.fits P) (by omega) _)
    (sc_w (X.fits P) (by rw [k₁.wr, b.wr]) (by omega))
    (fun j hj i hi => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))
    (fun i hi j hj hij => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)))
    fun t₂ ⟨k₂, x₂⟩ sy₂ => ⟨s, P, p, b₁.wb (X.fits P) k₂ (by rw [xorAt_length]; omega) x₂, sy₂.trans sy⟩

include X cG hF hf in
theorem roundT_ct {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub) :
    RelCT isa (Two (MgfRT S vf Pre Pub G.D src srcLen dst dstLen)) (roundT f j) fun _ _ => True := by
  have F := hfits hG
  obtain ⟨_, _, _, _, _⟩ := offs
  have hfs := hf.fs
  have hfd := hf.fd
  have p0 : ∀ {Φ : State × Nat → State → Prop},
      (∀ ac t, Φ ac t → MgfRT S vf Pre Pub G.D src srcLen dst dstLen ac t) → Pins Φ [] :=
    fun h ac t₁ t₂ h₁ h₂ => ⟨((mgfRT_pins X h) ac t₁ t₂ h₁ h₂).1, fun _ h => nomatch h⟩
  let M := MgfRT S vf Pre Pub G.D src srcLen dst dstLen
  have pres : ∀ {t t' : State}, (∀ r ∈ preserved, t'.gpr r = t.gpr r) →
      ∀ r ∈ [Reg.s6, .s7, .s8, .s9, .s10, .s11], t'.gpr r = t.gpr r :=
    fun h r hr => h r (by revert r; decide)
  -- A state after the load of a table's function's address keeps `M`'s `Base`.
  have btT : ∀ {ac t u}, M ac t → Only [.t1] t u → u.syms = t.syms → BT S vf Pre Pub ac.1 u :=
    fun {ac t u} h o y => let ⟨s, P, p, b, sy⟩ := h.1; ⟨s, P, p, b.only (X.fits P) o, y.trans sy⟩
  -- `init`.
  refine two_seq (Ψ := fun ac t => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt) (st_taint (p0 fun _ _ h => h))
    (fun ac t h => WP.of_syms (wp_addi (imm := oSt) fun t' o e => wp_nil fun sy =>
      let ⟨s, P, p, b, y⟩ := h.1
      ⟨h.keep ⟨s, P, p, b.only (X.fits P) o, sy.trans y⟩ (fun r hr => o.gpr r (by revert r; decide)),
        by rw [e, b.s0, (X.S p)]⟩)) ?_
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 0) (by decide)
    (fun P p => ⟨(A.tab P).ok.i, by rw [Nat.mul_zero, BitVec.add_zero]; exact (A.tab P).mem.1, A.ai p⟩)
    (init_ct (S := S) (vf := vf) cG fun u₁ u₂ hp => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ := hp
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := (btT h₁.1 o₁ y₁)
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := (btT h₂.1 o₂ y₂)
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [o₁.get .a0, h₁.2, (X.S p₁)], X.fits P₂, b₂,
      by rw [o₂.get .a0, h₂.2, (X.S p₂)], by rw [o₁.get .a0, o₂.get .a0, h₁.2, h₂.2],
      (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
  · obtain ⟨hm, h0⟩ := h
    obtain ⟨s, P, p, b, sy⟩ := hm.1
    exact WP.mono (initT_ok (X.fits P) (A.tab P) hG hF b sy (by rw [h0, (X.S p)])) fun t' ⟨⟨b', g', _⟩, sy'⟩ =>
      hm.keep ⟨s, P, p, b', sy'⟩ (pres g')
  -- `update` with `src`.
  let U₁ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt ∧
    t.gpr .a1 = 0 ∧ t.gpr .a2 = off (S ac.1) src ∧ t.gpr .a3 = BitVec.ofNat 64 srcLen
  refine two_seq (Ψ := U₁) (upd1_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ =>
      wp_mov fun t₃ o₃ e₃ => wp_mov fun t₄ o₄ e₄ => wp_nil fun sy => ?_)
    have k : Only [.a0, .a1, .a2, .a3] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
    obtain ⟨s, P, p, b, y⟩ := h.1
    refine ⟨h.keep ⟨s, P, p, b.only (X.fits P) k, sy.trans y⟩ (fun r hr => k.gpr r (by revert r; decide)),
      ?_, ?_, ?_, ?_⟩
    · rw [o₄.get .a0, o₃.get .a0, o₂.get .a0, e₁, b.s0, (X.S p)]
    · rw [o₄.get .a1, o₃.get .a1, e₂]; rfl
    · rw [o₄.get .a2, e₃, o₂.get .s6, o₁.get .s6, h.2.1]
    · rw [e₄, o₃.get .s7, o₂.get .s7, o₁.get .s7, h.2.2.1]
  have uargs : ∀ {ac : State × Nat} {t : State}, U₁ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) src) srcLen ∧ Pub ac.1 s ∧ t.syms = s.syms := fun {ac t} h => by
    obtain ⟨hm, h0, -, h2, h3⟩ := h
    obtain ⟨s, P, p, b, y⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h0, (X.S p)], by rw [h2, (X.S p)],
      by rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega)),
      sdis (.inl (by omega)) (by omega) (by omega), cR_dis (X.fits P) (by omega)⟩, p, y⟩
  have uargsT : ∀ {U : State × Nat → State → Prop}, (∀ {ac t}, U ac t → ∃ s d l, Pre s ∧ UpdArgs S vf G s t d l ∧
      Pub ac.1 s ∧ t.syms = s.syms) → ∀ {ac : State × Nat} {t u : State}, U ac t → Only [.t1] t u →
      ∃ s d l, UpdArgs S vf G s u d l ∧ Pub ac.1 s := fun {U} hU {ac t u} h o => by
    obtain ⟨s, d, l, P, A', p, -⟩ := hU h
    exact ⟨s, d, l, ⟨A'.P, A'.b.only A'.P o, by rw [o.get .a0]; exact A'.h0, by rw [o.get .a2]; exact A'.h2,
      by rw [o.get .a3]; exact A'.h3, by rw [o.rd, o.wr]; exact A'.hdc, A'.hd₁, A'.hd₃⟩, p⟩
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 1) (by decide)
    (fun P p => ⟨(A.tab P).ok.u, by rw [Nat.mul_one]; exact (A.tab P).mem.2.1, A.au p⟩)
    (upd_ct (S := S) (vf := vf) cG hF fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, _⟩, ⟨t₂, h₂, o₂, _⟩⟩ => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨s₁, d₁, l₁, A₁, p₁⟩ := uargsT (U := U₁) (fun h => let ⟨s, P, A', p, y⟩ := uargs h; ⟨s, _, _, P, A', p, y⟩)
      h₁ o₁
    obtain ⟨s₂, d₂, l₂, A₂, p₂⟩ := uargsT (U := U₁) (fun h => let ⟨s, P, A', p, y⟩ := uargs h; ⟨s, _, _, P, A', p, y⟩)
      h₂ o₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [o₁.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      o₂.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, P, A', p, y⟩ := uargs h
    exact WP.mono (updT_ok A'.P (A.tab P) hG hF A'.b y A'.h0 A'.h2 A'.h3 A'.hdc A'.hd₁ A'.hd₃)
      fun t' ⟨⟨b', g', _⟩, y'⟩ => h.1.keep ⟨s, P, p, b', y'⟩ (pres g')
  -- The counter, and `update` with it.
  let U₂ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt ∧
    t.gpr .a1 = BitVec.ofNat 64 srcLen ∧ t.gpr .a2 = off (S ac.1) oCtr ∧ t.gpr .a3 = BitVec.ofNat 64 4
  have hD0 := hG.hD0
  refine two_seq (Ψ := U₂) (ctr_taint (pins_monoT (mgfRT_pins X fun _ _ h => h))) (fun ac t h => ?_) ?_
  · obtain ⟨s, P, p, b, y⟩ := h.1
    have hc : ac.2 < 2 ^ 32 := by
      have := h.2.2.2.2.2.2.2; have := Nat.le_mul_of_pos_right ac.2 hD0; omega
    exact WP.mono_syms (ctr_ok (X.fits P) b h.2.2.2.2.2.1 hc) fun t' ⟨b', g', _, x0, x1, x2, x3⟩ y' =>
      ⟨h.keep ⟨s, P, p, b', y'.trans y⟩ (pres g'), by rw [x0, (X.S p)], by rw [x1, h.2.2.1], by rw [x2, (X.S p)],
        x3⟩
  have cargs : ∀ {ac : State × Nat} {t : State}, U₂ ac t →
      ∃ s, Pre s ∧ UpdArgs S vf G s t (off (S s) oCtr) 4 ∧ Pub ac.1 s ∧ t.syms = s.syms := fun {ac t} h => by
    obtain ⟨hm, h0, -, h2, h3⟩ := h
    obtain ⟨s, P, p, b, y⟩ := hm.1
    exact ⟨s, P, ⟨X.fits P, b, by rw [h0, (X.S p)], by rw [h2, (X.S p)], by rw [h3]; rfl,
      Covers.right (by rw [b.wr]; exact sc_cov (X.fits P) (by omega)),
      sdis (.inr (by omega)) (by omega) (by omega), cR_dis (X.fits P) (by omega)⟩, p, y⟩
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 1) (by decide)
    (fun P p => ⟨(A.tab P).ok.u, by rw [Nat.mul_one]; exact (A.tab P).mem.2.1, A.au p⟩)
    (upd_ct (S := S) (vf := vf) cG hF fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, _⟩, ⟨t₂, h₂, o₂, _⟩⟩ => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨s₁, d₁, l₁, A₁, p₁⟩ := uargsT (U := U₂) (fun h => let ⟨s, P, A', p, y⟩ := cargs h; ⟨s, _, _, P, A', p, y⟩)
      h₁ o₁
    obtain ⟨s₂, d₂, l₂, A₂, p₂⟩ := uargsT (U := U₂) (fun h => let ⟨s, P, A', p, y⟩ := cargs h; ⟨s, _, _, P, A', p, y⟩)
      h₂ o₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [o₁.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      o₂.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, P, A', p, y⟩ := cargs h
    exact WP.mono (updT_ok A'.P (A.tab P) hG hF A'.b y A'.h0 A'.h2 A'.h3 A'.hdc A'.hd₁ A'.hd₃)
      fun t' ⟨⟨b', g', _⟩, y'⟩ => h.1.keep ⟨s, P, p, b', y'⟩ (pres g')
  -- `finalize`.
  let U₃ := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt ∧
    t.gpr .a1 = BitVec.ofNat 64 srcLen + BitVec.ofNat 64 4 ∧ t.gpr .a2 = off (S ac.1) oDig
  refine two_seq (Ψ := U₃) (r4_taint (p0 fun _ _ h => h)) (fun ac t h => ?_) ?_
  · refine WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_addi (imm := 4) fun t₂ o₂ e₂ =>
      wp_addi (imm := oDig) fun t₃ o₃ e₃ => wp_nil fun sy => ?_)
    have k : Only [.a0, .a1, .a2] t t₃ := (o₁.trans (o₂.trans o₃)).mono
    obtain ⟨s, P, p, b, y⟩ := h.1
    refine ⟨h.keep ⟨s, P, p, b.only (X.fits P) k, sy.trans y⟩ (fun r hr => k.gpr r (by revert r; decide)),
      ?_, ?_, ?_⟩
    · rw [o₃.get .a0, o₂.get .a0, e₁, b.s0, (X.S p)]
    · rw [o₃.get .a1, e₂, o₁.get .s7, h.2.2.1]
    · rw [e₃, o₂.get .s0, o₁.get .s0, b.s0, (X.S p)]
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 2) (by decide)
    (fun P p => ⟨(A.tab P).ok.f, by rw [show 8 * 2 = 16 from rfl]; exact (A.tab P).mem.2.2, A.af p⟩)
    (fin_ct (S := S) (vf := vf) cG hF fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_))
    (fun ac t h => ?_) ?_
  · have ⟨_, x0, x1, x2⟩ := h₁
    have ⟨_, y0, y1, y2⟩ := h₂
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := btT h₁.1 o₁ y₁
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := btT h₂.1 o₂ y₂
    have g : ∀ {t u : State}, Only [.t1] t u → ∀ r ∈ [Reg.a0, .a1, .a2], u.gpr r = t.gpr r :=
      fun o r hr => o.gpr r (by revert r; decide)
    refine ⟨s₁, s₂, ⟨X.fits P₁, b₁, by rw [g o₁ _ (by decide), x0, (X.S p₁)],
        by rw [g o₁ _ (by decide), x2, (X.S p₁)]⟩,
      ⟨X.fits P₂, b₂, by rw [g o₂ _ (by decide), y0, (X.S p₂)], by rw [g o₂ _ (by decide), y2, (X.S p₂)]⟩,
      fun r hr => ?_, (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
    rw [g o₁ r hr, g o₂ r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [x0.trans y0.symm, x1.trans y1.symm, x2.trans y2.symm]
  · obtain ⟨hm, h0, -, h2⟩ := h
    obtain ⟨s, P, p, b, y⟩ := hm.1
    exact WP.mono (finT_ok (X.fits P) (A.tab P) hG hF b y (by rw [h0, (X.S p)]) (by rw [h2, (X.S p)]))
      fun t' ⟨⟨b', g', _⟩, y'⟩ => hm.keep ⟨s, P, p, b', y'⟩ (pres g')
  -- Into `dst`, and the next counter.
  have bD : ∀ {a s}, Pre s → Pub a s → s.mem.readW (stackArg s j + BitVec.ofNat 64 (8 * 4)) 64 =
      BitVec.ofNat 64 G.D := fun P _ => (A.tab P).d
  have xo : RelCT isa (Two M) (xorOutT j) fun _ _ => True := by
    show RelCT isa _ (.seq (.block (tword .a6 j 4 ++ xorRest)) (Impl.Bignum.RISCV64.countLoop .a6 xorBody)) _
    refine RelCT.seq_block_append (RelCT.seq (tword_two X A (Φ := M) (fun ac t h => h.1) (d := .a6) (.inl rfl)
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
    show RelCT isa _ (.block (tword .t1 j 4 ++ nextRest)) _
    refine RelCT.block_append (RelCT.seq (tword_two X A (fun _ _ h => h) (d := .t1) (.inr (.inl rfl)) (k := 4) (by decide)
      (v := fun _ => BitVec.ofNat 64 G.D) bD) (nextRest_taint fun ac u₁ u₂ hu₁ hu₂ => ?_))
    obtain ⟨t₁, h₁, o₁, _⟩ := hu₁
    obtain ⟨t₂, h₂, o₂, _⟩ := hu₂
    exact ⟨by rw [o₁.sp, o₂.sp]; exact (h₁.b.spS X).trans (h₂.b.spS X).symm, fun _ h => nomatch h⟩
  exact two_seq (Ψ := fun (ac : State × Nat) t => BT S vf Pre Pub ac.1 t) xo (fun ac t h => xorOutT_base X hG hf A h)
    nc

/-- MGF1's arguments in `s6`–`s9`, from the anchor. -/
def MgfAT (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (src srcLen dst dstLen : Nat) (a t : State) : Prop :=
  ∃ s, Pre s ∧ Pub a s ∧ Base S vf s t ∧ t.syms = s.syms ∧ t.gpr .s6 = off (S a) src ∧
    t.gpr .s7 = BitVec.ofNat 64 srcLen ∧ t.gpr .s8 = off (S a) dst ∧
    t.gpr .s9 = BitVec.ofNat 64 dstLen

variable {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)

/-- After `c` rounds, in a run: `MgfIT` for some view, and the counter below
the end. -/
def MgfLT (S : State → Addr) (vf : State → Reg → BitVec 64) (Pre : State → Prop) (Pub : State → State → Prop)
    (G : Hash) (Gs : Spec.Mgf1.Hash) (src srcLen dst dstLen : Nat) (ac : State × Nat) (t : State) : Prop :=
  ∃ s V, Pre s ∧ Pub ac.1 s ∧
    MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D ac.2 t ∧
      ac.2 * G.D < dstLen

include X in
theorem mgfLT_r {ac : State × Nat} {t : State} (h : MgfLT S vf Pre Pub G Gs src srcLen dst dstLen ac t) :
    MgfRT S vf Pre Pub G.D src srcLen dst dstLen ac t := by
  obtain ⟨s, V, P, p, I, hc⟩ := h
  exact ⟨⟨s, P, p, I.base, I.sy⟩, by rw [I.s6, (X.S p)], I.s7, by rw [I.s8, (X.S p)], I.s9, I.s10, I.s11, hc⟩

include X cG hF hf hGh hGl hGv in
theorem mgfXorT_ctS {f : Fns} {j : Nat} (A : TabA G f j S Pre Pub) :
    RelCT isa (Two (MgfAT S vf Pre Pub src srcLen dst dstLen)) (mgfXorT f j) fun _ _ => True := by
  have hD0 := hG.hD0
  have hpos := hf.pos
  let L := MgfLT S vf Pre Pub G Gs src srcLen dst dstLen
  let Ln := fun (n : Nat) (ac : State × Nat) (t : State) => L ac t ∧ n = dstLen - ac.2 * G.D
  have step : ∀ n, RelCT isa (Two (Ln n)) (roundT f j) fun s₁ s₂ =>
      isa.eval (.nonzero .t1) s₁ = isa.eval (.nonzero .t1) s₂ ∧
      (isa.eval (.nonzero .t1) s₁ = some false → True) ∧
      (isa.eval (.nonzero .t1) s₁ = some true → ∃ m < n, Two (Ln m) s₁ s₂) := fun n => by
    have h := two_post (Φ := Ln n) (Ψ := fun ac t => (t.gpr .t1 != 0) = decide ((ac.2 + 1) * G.D < dstLen) ∧
        ∃ s V, Pre s ∧ Pub ac.1 s ∧
          MgfIT S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D (ac.2 + 1) t ∧
          n = dstLen - ac.2 * G.D)
      ((roundT_ct X hG cG hF hf A).mono (fun _ _ ⟨ac, h₁, h₂⟩ => ⟨ac, mgfLT_r X h₁.1, mgfLT_r X h₂.1⟩)
        fun _ _ h => h)
      (fun ac t ⟨⟨s, V, P, p, I, hc⟩, hn⟩ => WP.mono (roundT_ok (X.fits P) hG hF (A.tab P) hGh hGl hGv hf I hc)
        fun t' ⟨hcf, I'⟩ => ⟨hcf, s, V, P, p, I', hn⟩)
    refine h.mono (fun _ _ h => h) fun s₁ s₂ ⟨ac, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ => ?_
    refine ⟨by rw [eval_nonzero, eval_nonzero, c₁, c₂], fun _ => trivial, fun ht => ?_⟩
    rw [eval_nonzero, c₁] at ht
    have hlt : (ac.2 + 1) * G.D < dstLen := by simpa using ht
    have hs1 : (ac.2 + 1) * G.D = ac.2 * G.D + G.D := Nat.succ_mul _ _
    obtain ⟨s, V, P, p, I, hn⟩ := h₁
    obtain ⟨s', V', P', p', I', -⟩ := h₂
    exact ⟨dstLen - (ac.2 + 1) * G.D, by omega, (ac.1, ac.2 + 1), ⟨⟨s, V, P, p, I, hlt⟩, rfl⟩,
      ⟨⟨s', V', P', p', I', hlt⟩, rfl⟩⟩
  refine RelCT.seq (two_post (Ψ := fun a t => L (a, 0) t) (mgfHead_taint fun a t₁ t₂ h₁ h₂ => ?_)
    (fun a t h => ?_)) ((RelCT.loop (fun n => Two (Ln n)) step (dstLen - 0 * G.D)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨(a, 0), ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩) fun _ _ h => h)
  · obtain ⟨_, -, p₁, b₁, -⟩ := h₁
    obtain ⟨_, -, p₂, b₂, -⟩ := h₂
    exact ⟨(Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm, fun _ h => nomatch h⟩
  · obtain ⟨s, P, p, b, sy, h6, h7, h8, h9⟩ := h
    refine WP.of_syms (wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ =>
      wp_nil fun sy₂ => ?_)
    have k₂ : Only [.s10, .s11] t t₂ := (o₁.trans o₂).mono
    exact ⟨s, view t.mem (S s), P, p, ⟨b.only (X.fits P) k₂, by rw [k₂.get .s6, h6, (X.S p)],
      by rw [k₂.get .s7, h7], by rw [k₂.get .s8, h8, (X.S p)], by rw [k₂.get .s9, h9],
      by rw [o₂.get .s10, e₁], by rw [e₂, Nat.zero_mul],
      fun o _ => by rw [mixV, ifn (by omega), k₂.mem], sy₂.trans sy⟩, by omega⟩

end

/-- `mgfXorT_ctS` for `Ok`. -/
theorem mgfXorT_ct {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop}
    {Pub : State → State → Prop} (X : Ok S vf Pre Pub) {G : Hash} (hG : HashOK G) (cG : HashCT hG)
    (hF : G.F ≤ 208) {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {f : Fns} {j : Nat}
    (A : TabA G f j S Pre Pub) :
    RelCT isa (Two (MgfAT S vf Pre Pub src srcLen dst dstLen)) (mgfXorT f j) fun _ _ => True :=
  mgfXorT_ctS X.s hG cG hF hf hGh hGl hGv A

/-! ## The label's hash through a table, in two runs -/

section Label
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {Pre : State → Prop} {Pub : State → State → Prop}
  (X : OkS S Pre Pub) {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208) {f : Fns} {j : Nat}
  (A : TabA H f j S Pre Pub)

include X cH hF A in
/-- `hashLabelT`, the label `N s` bytes at `L s`, in two runs with the hash
function `H` of the table that is our stack argument `j`, with `R` (of
registers the calls keep) besides `BT`: `update`'s and `finalize`'s
arguments set by `ua` and `fa` (`wu`, `wf`), its blocks by the taint
analysis (`cu`, `cf`), its calls by `init_ct`, `upd_ct`, `fin_ct` through
the table (`tcall_two`). -/
theorem hashLabelT_ct {ua fa : List Instr} {R : State × Nat → State → Prop} {L : State → Addr} {N : State → Nat}
    (hR : ∀ ac t t', R ac t → (∀ r ∈ preserved, t'.gpr r = t.gpr r) → R ac t')
    (hpub : ∀ {a s}, Pre s → Pub a s → L s = L a ∧ N s = N a)
    (hlab : ∀ {s}, Pre s → (⟨L s, N s⟩ : Region) ∈ s.rd ∧ Region.Disjoint ⟨L s, N s⟩ ⟨off (S s) oSt, H.S⟩ ∧
      (cR s).Disjoint ⟨L s, N s⟩ ∧ N s < 2 ^ 64)
    (cu : ∀ {Φ : State × Nat → State → Prop}, Pins Φ [] → RelCT isa (Two Φ) (.block ua) fun _ _ => True)
    (cf : ∀ {Φ : State × Nat → State → Prop}, Pins Φ [] → RelCT isa (Two Φ) (.block fa) fun _ _ => True)
    (wu : ∀ ac t, BT S vf Pre Pub ac.1 t → R ac t → WP isa (.block ua) t fun t' => BT S vf Pre Pub ac.1 t' ∧
      R ac t' ∧ t'.gpr .a0 = off (S ac.1) oSt ∧ t'.gpr .a1 = 0 ∧ t'.gpr .a2 = L ac.1 ∧
      t'.gpr .a3 = BitVec.ofNat 64 (N ac.1))
    (wf : ∀ ac t, BT S vf Pre Pub ac.1 t → R ac t → WP isa (.block fa) t fun t' => BT S vf Pre Pub ac.1 t' ∧
      t'.gpr .a0 = off (S ac.1) oSt ∧ t'.gpr .a1 = BitVec.ofNat 64 (N ac.1) ∧ t'.gpr .a2 = off (S ac.1) oDig) :
    RelCT isa (Two fun (ac : State × Nat) t => BT S vf Pre Pub ac.1 t ∧ R ac t) (hashLabelT f j ua fa)
      fun _ _ => True := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  let M : State × Nat → State → Prop := fun ac t => BT S vf Pre Pub ac.1 t ∧ R ac t
  have p0 : ∀ {Φ : State × Nat → State → Prop}, (∀ ac t, Φ ac t → BT S vf Pre Pub ac.1 t) → Pins Φ [] :=
    fun h ac t₁ t₂ h₁ h₂ => ⟨((h ac t₁ h₁).b.spS X).trans ((h ac t₂ h₂).b.spS X).symm, fun _ h => nomatch h⟩
  have btT : ∀ {ac : State × Nat} {t u : State}, BT S vf Pre Pub ac.1 t → Only [.t1] t u → u.syms = t.syms →
      BT S vf Pre Pub ac.1 u :=
    fun {ac t u} h o y => let ⟨s, P, p, b, sy⟩ := h; ⟨s, P, p, b.only (X.fits P) o, y.trans sy⟩
  -- `init`.
  refine two_seq (Ψ := fun ac t => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt) (st_taint (p0 fun _ _ h => h.1))
    (fun ac t h => WP.of_syms (wp_addi (imm := oSt) fun t' o e => wp_nil fun sy =>
      let ⟨s, P, p, b, y⟩ := h.1
      ⟨⟨⟨s, P, p, b.only (X.fits P) o, sy.trans y⟩, hR ac t t' h.2 fun r hr => o.gpr r (by revert r; decide)⟩,
        by rw [e, b.s0, (X.S p)]⟩)) ?_
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 0) (by decide)
    (fun P p => ⟨(A.tab P).ok.i, by rw [Nat.mul_zero, BitVec.add_zero]; exact (A.tab P).mem.1, A.ai p⟩)
    (init_ct (S := S) (vf := vf) cH fun u₁ u₂ hp => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ := hp
    obtain ⟨s₁, P₁, p₁, b₁, -⟩ := btT h₁.1.1 o₁ y₁
    obtain ⟨s₂, P₂, p₂, b₂, -⟩ := btT h₂.1.1 o₂ y₂
    exact ⟨s₁, s₂, X.fits P₁, b₁, by rw [o₁.get .a0, h₁.2, (X.S p₁)], X.fits P₂, b₂,
      by rw [o₂.get .a0, h₂.2, (X.S p₂)], by rw [o₁.get .a0, o₂.get .a0, h₁.2, h₂.2],
      (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
  · obtain ⟨⟨⟨s, P, p, b, sy⟩, r⟩, h0⟩ := h
    exact WP.mono (initT_ok (X.fits P) (A.tab P) hH hF b sy (by rw [h0, (X.S p)])) fun t' ⟨⟨b', g', _⟩, sy'⟩ =>
      ⟨⟨s, P, p, b', sy'⟩, hR ac t t' r g'⟩
  -- `update` with the label.
  let U := fun (ac : State × Nat) (t : State) => M ac t ∧ t.gpr .a0 = off (S ac.1) oSt ∧ t.gpr .a1 = 0 ∧
    t.gpr .a2 = L ac.1 ∧ t.gpr .a3 = BitVec.ofNat 64 (N ac.1)
  refine two_seq (Ψ := U) (cu (p0 fun _ _ h => h.1)) (fun ac t h => WP.mono (wu ac t h.1 h.2)
    fun t' ⟨b', r', h0, h1, h2, h3⟩ => ⟨⟨b', r'⟩, h0, h1, h2, h3⟩) ?_
  have uargs : ∀ {ac : State × Nat} {t u : State}, U ac t → Only [.t1] t u → u.syms = t.syms →
      ∃ s, Pre s ∧ UpdArgs S vf H s u (L s) (N s) ∧ Pub ac.1 s ∧ u.syms = s.syms := fun {ac t u} h o y => by
    obtain ⟨⟨hm, _⟩, h0, -, h2, h3⟩ := h
    obtain ⟨s, P, p, b, sy⟩ := btT hm o y
    obtain ⟨el, en⟩ := hpub P p
    obtain ⟨hl, d₁, d₃, hN⟩ := hlab P
    exact ⟨s, P, ⟨X.fits P, b, by rw [o.get .a0, h0, (X.S p)], by rw [o.get .a2, h2, el],
      by rw [o.get .a3, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← en]; exact hN), en],
      Covers.left (by rw [b.rd]; exact Covers.of_mem fun r hr => (List.mem_singleton.mp hr) ▸ hl), d₁, d₃⟩, p,
      sy⟩
  refine two_seq (Ψ := M) (tcall_two X A (fun ac t h => h.1.1) (k := 1) (by decide)
    (fun P p => ⟨(A.tab P).ok.u, by rw [Nat.mul_one]; exact (A.tab P).mem.2.1, A.au p⟩)
    (upd_ct (S := S) (vf := vf) cH hF fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_)) (fun ac t h => ?_) ?_
  · obtain ⟨s₁, -, A₁, p₁, -⟩ := uargs h₁ o₁ y₁
    obtain ⟨s₂, -, A₂, p₂, -⟩ := uargs h₂ o₂ y₂
    refine ⟨s₁, s₂, _, _, _, _, A₁, A₂, fun r hr => ?_, (Base.spA X p₁ A₁.b).trans (Base.spA X p₂ A₂.b).symm⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [o₁.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      o₂.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm]
  · obtain ⟨s, P, A', p, y⟩ := uargs h (Only.refl _ t) rfl
    exact WP.mono (updT_ok A'.P (A.tab P) hH hF A'.b y A'.h0 A'.h2 A'.h3 A'.hdc A'.hd₁ A'.hd₃)
      fun t' ⟨⟨b', g', _⟩, y'⟩ => ⟨⟨s, P, p, b', y'⟩, hR ac t t' h.1.2 g'⟩
  -- `finalize`.
  let U₃ := fun (ac : State × Nat) (t : State) => BT S vf Pre Pub ac.1 t ∧ t.gpr .a0 = off (S ac.1) oSt ∧
    t.gpr .a1 = BitVec.ofNat 64 (N ac.1) ∧ t.gpr .a2 = off (S ac.1) oDig
  refine two_seq (Ψ := U₃) (cf (p0 fun _ _ h => h.1)) (fun ac t h => wf ac t h.1 h.2) ?_
  refine tcall_two X A (fun ac t h => h.1) (k := 2) (by decide)
    (fun P p => ⟨(A.tab P).ok.f, by rw [show 8 * 2 = 16 from rfl]; exact (A.tab P).mem.2.2, A.af p⟩)
    (fin_ct (S := S) (vf := vf) cH hF fun u₁ u₂ ⟨ac, ⟨t₁, h₁, o₁, y₁⟩, ⟨t₂, h₂, o₂, y₂⟩⟩ => ?_)
  have ⟨_, x0, x1, x2⟩ := h₁
  have ⟨_, z0, z1, z2⟩ := h₂
  obtain ⟨s₁, P₁, p₁, b₁, -⟩ := btT h₁.1 o₁ y₁
  obtain ⟨s₂, P₂, p₂, b₂, -⟩ := btT h₂.1 o₂ y₂
  have g : ∀ {t u : State}, Only [.t1] t u → ∀ r ∈ [Reg.a0, .a1, .a2], u.gpr r = t.gpr r :=
    fun o r hr => o.gpr r (by revert r; decide)
  refine ⟨s₁, s₂, ⟨X.fits P₁, b₁, by rw [g o₁ _ (by decide), x0, (X.S p₁)], by rw [g o₁ _ (by decide), x2, (X.S p₁)]⟩,
    ⟨X.fits P₂, b₂, by rw [g o₂ _ (by decide), z0, (X.S p₂)], by rw [g o₂ _ (by decide), z2, (X.S p₂)]⟩,
    fun r hr => ?_, (Base.spA X p₁ b₁).trans (Base.spA X p₂ b₂).symm⟩
  rw [g o₁ r hr, g o₂ r hr]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [x0.trans z0.symm, x1.trans z1.symm, x2.trans z2.symm]

end Label

end VG.Proof.RsaOaep.RISCV64
