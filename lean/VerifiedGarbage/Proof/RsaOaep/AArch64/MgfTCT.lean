module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# RSAES-OAEP on AArch64: MGF1 with the hash function of a table, in constant time

As `mgfXor_tr` (`Proof/RsaOaep/AArch64/MgfCT.lean`), for `Table.mgfXor`: the
pieces between calls are checked by the taint analysis as there (the digest
length is now loaded from a slot, so no immediate depends on the hash
function), and each indirect call is related across the two runs by
`RelCT.icalls_of_call` (`lr_tcall`): both runs hold the same table, at the
same address, and their functions are at the same addresses (`MXT`'s `ai`,
`au` and `af`), so both call the same function, whose call is constant time
as before (`lr_init`, `lr_upd`, `lr_fin`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Table

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns tcall tabArg tabHead)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs initArgs updSrcArgs updCtrArgs finArgs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Stream Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

/-! ## An indirect call in two runs -/

/-- The indirect call of the table's function `j` in two runs whose table
(word 32) is at `p` and whose function `n` is at `a`: of `n` in both, whose
call is constant time from `X`, which a load into `x16` keeps. -/
theorem lr_tcall {F S p a : Addr} {X : (Nat → BitVec 64) → State → Prop} (j : Nat) {ts : List (String × Prog isa)}
    {n : String} {c : Prog isa}
    (hv : ∀ W t, X W t → W 32 = p ∧ InRegions (t.rd ++ t.wr) (off p (8 * j)) 8 ∧
      t.mem.readW (off p (8 * j)) 64 = a ∧ ts.find? (fun q => t.syms q.1 == a) = some (n, c))
    (hk : ∀ W (t u : State), X W t → u.mem = t.mem → u.syms = t.syms → u.rd = t.rd → u.wr = t.wr →
      u.sp = t.sp → u.v = t.v → (∀ r, r ≠ .x16 → u.gpr r = t.gpr r) → X W u)
    {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs []) (.block [.ldrSp .x16 sTab]) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.x16]) (.block [.ldr .x .x16 .x16 (8 * j)]) h₂).isSome = true)
    (hj : 8 * j < 32768)
    (hcall : RelCT isa (LR F S X) (.call n c) fun _ _ => True) :
    RelCT isa (LR F S X) (tcall sTab j ts) fun _ _ => True := by
  unfold tcall
  rw [show ([.ldrSp .x16 sTab, .ldr .x .x16 .x16 (8 * j)] : List Instr) =
    [.ldrSp .x16 sTab] ++ [.ldr .x .x16 .x16 (8 * j)] from rfl]
  apply RelCT.seq_block_append
  refine (lr_wp (X' := fun W t => X W t ∧ t.gpr .x16 = p) (lr_taint [] t₁ nopin)
    fun t V W L R hx => ?_).seq ?_
  · have h256 : InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 256) 8 := L.ld (d := 256) (by decide)
    have r32 := R.rd8 (d := 256) (k := 32) rfl (by decide) (hv W t hx).1
    refine WP.mono (Q := fun (u : State) => u.mem = t.mem ∧ u.syms = t.syms ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
        u.sp = t.sp ∧ u.v = t.v ∧ (∀ r, r ≠ .x16 → u.gpr r = t.gpr r) ∧ u.gpr .x16 = p) ?_
      fun u ⟨hm, hs, hrd, hwr, hsp, hvv, hg, h16⟩ =>
        ⟨V, W, L.congr hsp hwr (by rw [hm]), hm ▸ R, hk W t u hx hm hs hrd hwr hsp hvv hg, h16⟩
    oaep_run [sTab, h256, L.sp, r32]
    and_intros <;> first | trivial | rfl | (intro r hr; simp [hr])
  refine (lr_wp (X' := fun W t => X W t ∧ t.gpr .x16 = a)
    (lr_taint [.x16] t₂ fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun t V W L R hx16 => ?_).seq ?_
  · obtain ⟨hx, h16⟩ := hx16
    obtain ⟨-, hrd, hw, -⟩ := hv W t hx
    refine WP.mono (Q := fun (u : State) => u.mem = t.mem ∧ u.syms = t.syms ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
        u.sp = t.sp ∧ u.v = t.v ∧ (∀ r, r ≠ .x16 → u.gpr r = t.gpr r) ∧ u.gpr .x16 = a) ?_
      fun u ⟨hm, hs, hrd', hwr, hsp, hvv, hg, h16'⟩ =>
        ⟨V, W, L.congr hsp hwr (by rw [hm]), hm ▸ R, hk W t u hx hm hs hrd' hwr hsp hvv hg, h16'⟩
    have hw' : t.mem.read (p + BitVec.ofNat 64 (8 * j)) 8 = a := by simpa [Mem.readW] using hw
    oaep_run [h16, hrd, hw', hj, Nat.mul_mod_right]
    and_intros <;> first | trivial | rfl | (intro r hr; simp [hr])
  cases ts with
  | nil =>
    exact RelCT.of_false fun s₁ s₂ ⟨⟨_, W, _, _, hx, _⟩, _⟩ => by simpa using (hv W s₁ hx).2.2.2
  | cons q ts =>
    refine RelCT.icalls_of_call (hcall.mono (fun _ _ ⟨⟨V₁, W₁, L₁, R₁, x₁, _⟩, ⟨V₂, W₂, L₂, R₂, x₂, _⟩⟩ =>
      ⟨⟨V₁, W₁, L₁, R₁, x₁⟩, ⟨V₂, W₂, L₂, R₂, x₂⟩⟩) fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨⟨V₁, W₁, L₁, R₁, x₁, a₁⟩, ⟨V₂, W₂, L₂, R₂, x₂, a₂⟩⟩
    exact ⟨a, by simp only [icall, a₁], by simp only [icall, a₂], (hv W₁ s₁ x₁).2.2.2,
      (hv W₂ s₂ x₂).2.2.2, rfl⟩

/-- The table at `p`, from the stack argument at `sArg` (`Tab`), and the
addresses of `G`'s functions, which both runs agree on. -/
def TabX (G : Stream) (f : Fns) (sArg : Nat) (F S p ai au af : Addr) (t : State) : Prop :=
  Tab G f F S p sArg t ∧ t.syms G.initN = ai ∧ t.syms G.updN = au ∧ t.syms G.finN = af

theorem TabX.step {G : Stream} {f : Fns} {sArg : Nat} {F S p ai au af : Addr} {t u : State}
    (h : TabX G f sArg F S p ai au af t) (hS : Step F S [] t u) (sy : u.syms = t.syms) :
    TabX G f sArg F S p ai au af u :=
  ⟨h.1.step hS sy, by rw [sy]; exact h.2.1, by rw [sy]; exact h.2.2.1, by rw [sy]; exact h.2.2.2⟩

/-! ## The points of a round -/

/-- The table, from MGF1's entry state, and the addresses of `G`'s `init`,
`update` and `finalize`, which both runs agree on. -/
structure TT (G : Stream) (f : Fns) (F S p ai au af : Addr) (t : State) : Prop where
  tab : ∃ u₀ sArg, Tab G f F S p sArg u₀ ∧ Step F S [] u₀ t ∧ t.syms = u₀.syms
  ai : t.syms G.initN = ai
  au : t.syms G.updN = au
  af : t.syms G.finN = af

theorem TT.at {G : Stream} {f : Fns} {F S p ai au af : Addr} {t : State} (h : TT G f F S p ai au af t) :
    TabAt G f p t := by
  obtain ⟨u₀, _, T, st, sy⟩ := h.tab
  exact T.at st sy

theorem TT.step {G : Stream} {f : Fns} {F S p ai au af : Addr} {t u : State} (h : TT G f F S p ai au af t)
    (st : Step F S [] t u) (sy : u.syms = t.syms) : TT G f F S p ai au af u := by
  obtain ⟨u₀, sA, T, st₀, sy₀⟩ := h.tab
  exact ⟨⟨u₀, sA, T, st₀.trans st, sy.trans sy₀⟩, by rw [sy]; exact h.ai, by rw [sy]; exact h.au,
    by rw [sy]; exact h.af⟩

/-- A state reached by a load into `x16`: what `TT` sees of it is the same. -/
theorem TT.congr {G : Stream} {f : Fns} {F S p ai au af : Addr} {t u : State} (h : TT G f F S p ai au af t)
    (hm : u.mem = t.mem) (hs : u.syms = t.syms) (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hv : u.v = t.v) (hcs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) : TT G f F S p ai au af u :=
  h.step (Step.blk [] hrd hwr hsp hv hcs hm) hs

/-- MGF1's slots, the table's, and the table, at the counter `c`. -/
def MXT (G : Stream) (f : Fns) (S p ai au af : Addr) (F : Addr) (src srcLen dst dstLen c : Nat)
    (W : Nat → BitVec 64) (t : State) : Prop :=
  MX S src srcLen dst dstLen G.D c W t ∧ W 32 = p ∧ W 33 = BitVec.ofNat 64 G.D ∧ TT G f F S p ai au af t

theorem MXT.congr {G : Stream} {f : Fns} {S p ai au af F : Addr} {src srcLen dst dstLen c : Nat}
    {W : Nat → BitVec 64} {t u : State} (h : MXT G f S p ai au af F src srcLen dst dstLen c W t)
    (hm : u.mem = t.mem) (hs : u.syms = t.syms) (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp)
    (hv : u.v = t.v) (hg : ∀ r, r ≠ .x16 → u.gpr r = t.gpr r) :
    MXT G f S p ai au af F src srcLen dst dstLen c W u :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.congr hm hs hrd hwr hsp hv fun r hr _ => hg r (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩

theorem MXT.step {G : Stream} {f : Fns} {S p ai au af F : Addr} {src srcLen dst dstLen c : Nat}
    {W : Nat → BitVec 64} {t u : State} (h : MXT G f S p ai au af F src srcLen dst dstLen c W t)
    (st : Step F S [] t u) (sy : u.syms = t.syms) : MXT G f S p ai au af F src srcLen dst dstLen c W u :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.step st sy⟩

variable {G : Stream} (hG : StreamOK G) {f : Fns}

/-- What an indirect call of the table's function needs of `X`, from `MXT`. -/
theorem mxt_hv {S p ai au af F : Addr} {src srcLen dst dstLen c : Nat} {Y : (Nat → BitVec 64) → State → Prop}
    {j : Nat} (hj : j < 3) {a : Addr} {n : String} {cn : Prog isa} {ts : List (String × Prog isa)}
    (hn : ∀ t, TT G f F S p ai au af t → TabAt G f p t → t.mem.readW (off p (8 * j)) 64 = a ∧ t.syms n = a ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, cn)) :
    ∀ W t, (MXT G f S p ai au af F src srcLen dst dstLen c W t ∧ Y W t) → W 32 = p ∧
      InRegions (t.rd ++ t.wr) (off p (8 * j)) 8 ∧ t.mem.readW (off p (8 * j)) 64 = a ∧
      ts.find? (fun q => t.syms q.1 == a) = some (n, cn) := by
  intro W t ⟨hx, _⟩
  obtain ⟨hr, hs, hf⟩ := hn t hx.2.2.2 hx.2.2.2.at
  exact ⟨hx.2.1, hx.2.2.2.at.rd j hj, hr, by rw [← hs]; exact hf⟩

include hG in
theorem roundT_tr {F S p ai au af : Addr} {src srcLen dst dstLen c : Nat} (hf : MFit src srcLen dst dstLen)
    (hc : c * G.D < dstLen) :
    RelCT isa (LR F S (MXT G f S p ai au af F src srcLen dst dstLen c))
      (Impl.RsaOaep.AArch64.Mgf1.Table.round lay sTab sD f)
      (LR F S fun W t => MXT G f S p ai au af F src srcLen dst dstLen (c + 1) W t ∧
        (t.gpr .x12 != 0) = decide ((c + 1) * G.D < dstLen)) := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 3520 := rfl
  have c5 : oRsa = 8192 := rfl
  have hfs := hf.fs
  have hfd := hf.fd
  have hdb := hf.dstB
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hzD
  let X := MXT G f S p ai au af F src srcLen dst dstLen c
  have hiN : ∀ t, TT G f F S p ai au af t → TabAt G f p t → t.mem.readW (off p (8 * 0)) 64 = ai ∧
      t.syms G.initN = ai ∧ f.init.find? (fun q => t.syms q.1 == t.syms G.initN) = some (G.initN, G.initC) :=
    fun t h T => ⟨T.mem.1.trans h.ai, h.ai, T.ok.i⟩
  have huN : ∀ t, TT G f F S p ai au af t → TabAt G f p t → t.mem.readW (off p (8 * 1)) 64 = au ∧
      t.syms G.updN = au ∧ f.upd.find? (fun q => t.syms q.1 == t.syms G.updN) = some (G.updN, G.updC) :=
    fun t h T => ⟨T.mem.2.1.trans h.au, h.au, T.ok.u⟩
  have hfN : ∀ t, TT G f F S p ai au af t → TabAt G f p t → t.mem.readW (off p (8 * 2)) 64 = af ∧
      t.syms G.finN = af ∧ f.fin.find? (fun q => t.syms q.1 == t.syms G.finN) = some (G.finN, G.finC) :=
    fun t h T => ⟨T.mem.2.2.trans h.af, h.af, T.ok.f⟩
  unfold Impl.RsaOaep.AArch64.Mgf1.Table.round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine (lr_wp (X' := fun W t => X W t ∧ t.gpr .x0 = off S oSt)
    (lr_taint [] (by taint_decide) nopin) fun t V W L R hx => WP.mono (wp_sy (initArgs_ok L []))
      fun u ⟨⟨Su, hm, x0⟩, sy⟩ => ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx.step Su sy, x0⟩).seq ?_
  refine (lr_wp (X' := X) (lr_tcall 0 (mxt_hv (by decide) hiN)
      (fun W t u ⟨hx, x0⟩ hm hs hrd hwr hsp hv hg => ⟨hx.congr hm hs hrd hwr hsp hv hg, (hg _ (by decide)).trans x0⟩)
      (by taint_decide) (by taint_decide) (by decide) (lr_init hG fun _ _ h => h.2))
    fun t V W L R ⟨hx, x0⟩ => WP.mono (wp_sy (initT_ok hG L R hx.2.1 hx.2.2.2.at x0))
      fun u ⟨⟨Lu, Su, Ru, _⟩, sy⟩ => ⟨_, W, Lu, Ru, hx.step Su sy⟩).seq ?_
  -- `update` with `src`.
  refine (lr_wp (X' := fun W t => X W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ t.gpr .x2 = off S src ∧ t.gpr .x3 = BitVec.ofNat 64 srcLen ∧
      t.gpr .x4 = off S oW) (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (wp_sy (updSrc_ok L R hx.1.1 [])) fun u ⟨⟨Su, hm, x0, x1, x2, x3, x4⟩, sy⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx.step Su sy, x0, x1, x2, x3, x4⟩).seq ?_
  refine (lr_wp (X' := X) (lr_tcall 1 (X := fun W t => X W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ t.gpr .x2 = off S src ∧ t.gpr .x3 = BitVec.ofNat 64 srcLen ∧
      t.gpr .x4 = off S oW) (mxt_hv (by decide) huN)
      (fun W t u ⟨hx, x0, x1, x2, x3, x4⟩ hm hs hrd hwr hsp hv hg => ⟨hx.congr hm hs hrd hwr hsp hv hg,
        (hg _ (by decide)).trans x0, (hg _ (by decide)).trans x1, (hg _ (by decide)).trans x2,
        (hg _ (by decide)).trans x3, (hg _ (by decide)).trans x4⟩)
      (by taint_decide) (by taint_decide) (by decide)
      (lr_upd hG (BitVec.ofNat 64 0) (a := src) (len := srcLen) (by omega) (by omega) (by omega) fun _ _ h => h.2))
    fun t V W L R ⟨hx, x0, _, x2, x3, x4⟩ => WP.mono (wp_sy (updT_ok hG L R hx.2.1 hx.2.2.2.at (by omega)
      (by omega) (by omega) x0 x2 x3 x4)) fun u ⟨⟨Lu, Su, Ru, _⟩, sy⟩ => ⟨_, W, Lu, Ru, hx.step Su sy⟩).seq ?_
  -- The counter, and `update` with it.
  refine (lr_wp (X' := fun W t => X W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 srcLen ∧ t.gpr .x2 = off S oCtr ∧ t.gpr .x3 = BitVec.ofNat 64 4 ∧
      t.gpr .x4 = off S oW) (by
        rw [updCtrArgs_eq]
        exact RelCT.block_append (lr_seq_tr [.x2] (fun _ => off S oCtr) (by taint_decide) (by taint_decide)
          fun t V W L R _ => WP.mono (scr_pin L .x2 (o := oCtr) (by decide)) fun u ⟨hs, x2⟩ =>
            ⟨hs, fun r hr => by rw [List.mem_singleton.mp hr]; exact x2⟩))
    fun t V W L R hx => WP.mono (wp_sy (updCtr_ok L R hx.1.1.hsl hx.1.2.1 (by omega) []))
      fun u ⟨⟨Lu, Su, Ru, x0, x1, x2, x3, x4⟩, sy⟩ => ⟨_, W, Lu, Ru, hx.step Su sy, x0, x1, x2, x3, x4⟩).seq ?_
  refine (lr_wp (X' := X) (lr_tcall 1 (X := fun W t => X W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 srcLen ∧ t.gpr .x2 = off S oCtr ∧ t.gpr .x3 = BitVec.ofNat 64 4 ∧
      t.gpr .x4 = off S oW) (mxt_hv (by decide) huN)
      (fun W t u ⟨hx, x0, x1, x2, x3, x4⟩ hm hs hrd hwr hsp hv hg => ⟨hx.congr hm hs hrd hwr hsp hv hg,
        (hg _ (by decide)).trans x0, (hg _ (by decide)).trans x1, (hg _ (by decide)).trans x2,
        (hg _ (by decide)).trans x3, (hg _ (by decide)).trans x4⟩)
      (by taint_decide) (by taint_decide) (by decide)
      (lr_upd hG (BitVec.ofNat 64 srcLen) (a := oCtr) (len := 4) (by omega) (by omega) (by omega) fun _ _ h => h.2))
    fun t V W L R ⟨hx, x0, _, x2, x3, x4⟩ => WP.mono (wp_sy (updT_ok hG L R hx.2.1 hx.2.2.2.at (a := oCtr)
      (len := 4) (by omega) (by omega) (by omega) x0 x2 x3 x4)) fun u ⟨⟨Lu, Su, Ru, _⟩, sy⟩ =>
        ⟨_, W, Lu, Ru, hx.step Su sy⟩).seq ?_
  -- `finalize`.
  refine (lr_wp (X' := fun W t => X W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 (srcLen + 4) ∧ t.gpr .x2 = off S oDig ∧ t.gpr .x3 = off S oW)
    (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (wp_sy (finA_ok L R hx.1.1.hsl [])) fun u ⟨⟨Su, hm, x0, x1, x2, x3⟩, sy⟩ =>
      ⟨V, W, L.congr Su.sp Su.wr (by rw [hm]), hm ▸ R, hx.step Su sy, x0, x1, x2, x3⟩).seq ?_
  refine (lr_wp (X' := X) (lr_tcall 2 (X := fun W t => X W t ∧ t.gpr .x0 = off S oSt ∧
      t.gpr .x1 = BitVec.ofNat 64 (srcLen + 4) ∧ t.gpr .x2 = off S oDig ∧ t.gpr .x3 = off S oW)
      (mxt_hv (by decide) hfN)
      (fun W t u ⟨hx, x0, x1, x2, x3⟩ hm hs hrd hwr hsp hv hg => ⟨hx.congr hm hs hrd hwr hsp hv hg,
        (hg _ (by decide)).trans x0, (hg _ (by decide)).trans x1, (hg _ (by decide)).trans x2,
        (hg _ (by decide)).trans x3⟩)
      (by taint_decide) (by taint_decide) (by decide)
      (lr_fin hG (BitVec.ofNat 64 (srcLen + 4)) (o := oDig) (.inr (by decide)) fun _ _ h => h.2))
    fun t V W L R ⟨hx, x0, _, x2, x3⟩ => WP.mono (wp_sy (finT_ok hG L R hx.2.1 hx.2.2.2.at (o := oDig)
      (.inr (by decide)) x0 x2 x3)) fun u ⟨⟨Lu, Su, Ru, _⟩, sy⟩ => ⟨_, W, Lu, Ru, hx.step Su sy⟩).seq ?_
  -- Into `dst`.
  refine (lr_wp (X' := X) (lr_seq_tr [.x11, .x12, .x14]
      (fun r => if r = .x11 then off S oDig else if r = .x12 then off S (dst + c * G.D)
        else BitVec.ofNat 64 (min G.D (dstLen - c * G.D)))
      (by taint_decide) (by taint_decide)
      fun t V W L R hx => WP.mono (xorHeadT_ok L R (D := G.D) (by omega) (by omega) hx.2.2.1 hx.1.1.hdst
        hx.1.1.hdl hx.1.2.2 hc []) fun u ⟨Su, _, x11, x12, x14⟩ => ⟨Su.sp, by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl) <;> simp [x11, x12, x14]⟩)
    fun t V W L R hx => WP.mono (wp_sy (xorOutT_ok L R hfd hzD (by omega) hx.2.2.1 hx.1.1.hdst hx.1.1.hdl
      hx.1.2.2 hc [])) fun u ⟨⟨Lu, Su, Ru⟩, sy⟩ => ⟨_, W, Lu, Ru, hx.step Su sy⟩).seq ?_
  -- The next counter.
  refine lr_wp (lr_taint [] (by taint_decide) nopin)
    fun t V W L R hx => WP.mono (wp_sy (nextCtrT_ok L R (D := G.D) hx.1.2.1 hx.1.2.2 hx.1.1.hdl hx.2.2.1
        (by omega) (by omega) []))
      fun u ⟨⟨Lu, Su, x12, Ru⟩, sy⟩ => ⟨_, _, Lu, Ru, ⟨⟨hx.1.1.of_eq fun k h1 h2 => by
        simp only [upd]; rw [ifn (by omega), ifn (by omega)], by simp [upd], by simp [upd, Nat.succ_mul]⟩,
        by simp only [upd]; exact hx.2.1, by simp only [upd]; exact hx.2.2.1, hx.2.2.2.step Su sy⟩,
        by rw [x12, Nat.succ_mul]⟩

include hG in
theorem mgfXorT_tr {F S p ai au af : Addr} {sArg : Nat} (hsa : sArg < 32768 ∧ sArg % 8 = 0)
    {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen)
    {X : (Nat → BitVec 64) → State → Prop}
    (hX : ∀ W t, X W t → MArgs W S src srcLen dst dstLen ∧ Tab G f F S p sArg t ∧
      t.syms G.initN = ai ∧ t.syms G.updN = au ∧ t.syms G.finN = af)
    {h₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htA : (taint.check (Taint.ofRegs []) (.block (tabArg sArg sTab)) h₁).isSome = true) :
    RelCT isa (LR F S X) (Impl.RsaOaep.AArch64.Mgf1.Table.mgfXor lay sArg sTab sD f) fun _ _ => True := by
  obtain ⟨-, -, -, -, hzD⟩ := sizes hG
  replace hzD : 0 < G.D := hzD
  have hN : 0 < (dstLen + G.D - 1) / G.D := (lt_ceil hzD).mpr (by have := hf.pos; omega)
  unfold Impl.RsaOaep.AArch64.Mgf1.Table.mgfXor seqs seqs
  -- The table's address to its slot, and in `x10`.
  refine (lr_wp (X' := fun W t => MArgs W S src srcLen dst dstLen ∧ W 32 = p ∧ TT G f F S p ai au af t ∧
      t.gpr .x10 = p) (lr_taint [] htA nopin) fun t V W L R hx => ?_).seq ?_
  · obtain ⟨hA, T, hai, hau, haf⟩ := hX W t hx
    refine WP.mono (wp_sy (tabArg_ok (G := G) hsa L R T)) fun u ⟨⟨Lu, Su, Ru, x10⟩, sy⟩ =>
      ⟨V, _, Lu, Ru, hA.of_eq fun k h1 h2 => by simp only [upd]; rw [ifn (by omega)], by simp [upd],
        ⟨⟨t, sArg, T, Su, sy⟩, by rw [sy]; exact hai, by rw [sy]; exact hau, by rw [sy]; exact haf⟩, x10⟩
  -- The digest length to its slot, the counter and `done` to 0.
  refine (lr_wp (X' := MXT G f S p ai au af F src srcLen dst dstLen 0)
    (lr_taint [.x10] (by taint_decide) fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2, h₂.2.2.2])
    fun t V W L R hx => ?_).seq ?_
  · obtain ⟨hA, h32, hT, x10⟩ := hx
    obtain ⟨u₀, _, T, st, sy⟩ := hT.tab
    have hrd : InRegions (t.rd ++ t.wr) (off p 32) 8 := by rw [st.rd, st.wr]; exact T.rdD
    have hD := (T.mem _ st.frame).2.1
    refine WP.mono (wp_sy (tabHead_ok (G := G) L R x10 hrd hD [] dst dstLen)) fun v ⟨I, syv⟩ => ?_
    obtain ⟨V', W', R', h17, h18, hW, -⟩ := I.rep
    refine ⟨V', W', I.L, R', ⟨(hA.of_eq fun k h1 h2 => by
        rw [hW k (by unfold nW frameBytes; omega) (by omega) (by omega)]; simp only [upd]; rw [ifn (by omega)]),
      h17, by rw [h18, Nat.zero_mul]⟩, ?_, ?_, hT.step I.st syv⟩
    · rw [hW 32 (by decide) (by decide) (by decide)]; simp only [upd]; exact h32
    · rw [hW 33 (by decide) (by decide) (by decide)]; simp [upd]
  -- The rounds.
  exact (count_ct hN (fun c => LR F S (MXT G f S p ai au af F src srcLen dst dstLen c)) fun c hc =>
    (roundT_tr hG hf ((lt_ceil hzD).mp hc)).mono (fun _ _ h => h)
      fun a b ⟨⟨Va, Wa, La, Ra, xa, ca⟩, ⟨Vb, Wb, Lb, Rb, xb, cb⟩⟩ =>
        ⟨⟨⟨Va, Wa, La, Ra, xa⟩, ⟨Vb, Wb, Lb, Rb, xb⟩⟩,
          by rw [ca]; exact decide_eq_decide.mpr (by rw [← lt_ceil hzD]; omega),
          by rw [cb]; exact decide_eq_decide.mpr (by rw [← lt_ceil hzD]; omega)⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.RsaOaep.AArch64.Table
