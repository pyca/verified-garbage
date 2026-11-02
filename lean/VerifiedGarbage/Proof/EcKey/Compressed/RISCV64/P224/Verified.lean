module

public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Main
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Main
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.P224.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# SEC 1 point conversion over P-224 on RISC-V: `Verified`

`compress_verified`: from `compress_ok`, with the times depending only on the
pointers (by taint tracking).

`decompress_verified`: from `decompress_ok`, under `abi.withConsts` of the
square root's table (`decRVC`). Its time depends on the public key, which
the contract allows (`leak`): the table's entries read are those of the
digits of `rhs`, which the bytes determine. Two runs with the same public
data (the pointers, the table's address, `rhs`) are related (`Two`) by the
correctness proof's states (`front_ok`, `digit_ok`): before the digits, after
each digit (which pins the digits found so far in `s4` and `s5`) and before
the root; each piece is checked by the taint analysis from the registers
those states pin (`RelCT`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.RISCV64.P224

open VG VG.RISCV64 VG.Impl.EcKey.Compressed.RISCV64
open VG.Impl.Ecdsa.RISCV64 (Cfg)
open VG.Proof.Weierstrass.RISCV64 (WsReg)
open VG.Proof.Ecdsa.RISCV64.P224 (W)

theorem compress_rv (s : State) (hs : compRV.pre s) :
    ∃ t s', Exec isa compressP224 s t s' ∧ abiPreserved s s' ∧ compRV.post s s' := by
  obtain ⟨t, s', he, h⟩ := compress_ok hs
  exact ⟨t, s', he, h⟩

theorem compress_ct : ConstantTime isa compRV.pre compRV.pub compressP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

/-- A state satisfying the preconditions, for an output of `n` bytes and an
input of `m`. -/
def convSat (n m : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, m⟩]
  wr := [⟨0x1000, n⟩, ⟨0x8000, 8192⟩]

theorem compress_verified :
    Verified RISCV64.target compressP224 (Spec.EcKey.P224.inst.compressPublicKeyContract RISCV64.abi) :=
  Verified.of_correct compress_rv compress_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
        have h' : match Spec.EcKey.compressPublicKey Spec.P224.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) 57) with
            | some bs => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 29 = bs
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 29 = List.replicate 29 0 := h
        generalize hq : Spec.EcKey.compressPublicKey _ _ = q
        have hq' : Spec.EcKey.compressPublicKey Spec.P224.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) 57) = q := hq
        rw [hq'] at h'
        rcases q with _ | z
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
          Spec.EcKey.Instance.compressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, compRV,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 29 57) }

/-! ## Decompression's contract -/

/-- The precondition by register, without the table. -/
def DPre0 (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 57⟩
  let pk : Region := ⟨s.gpr .a1, 29⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 29 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0

/-- `vg_ec_p224_decompress_public_key(out = a0, public = a1, scratch = a2)`, by
register, without the table. -/
def decRV : Contract isa where
  pre := DPre0
  post := DPostC
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    (Spec.EcKey.bytesAt s₁.mem (s₁.gpr .a1) 29).map (·.toNat) = (Spec.EcKey.bytesAt s₂.mem (s₂.gpr .a1) 29).map (·.toNat)

/-- `decRV` with the table (`abi.withConsts`). -/
def decRVC : Contract isa where
  pre s := decRV.pre (stripConsts sqrtConsts s) ∧ ConstsOk sqrtConsts 0 s
  post := decRV.post
  pub s₁ s₂ := decRV.pub s₁ s₂ ∧ s₁.syms sqrtSym = s₂.syms sqrtSym

/-- The precondition the proof of correctness takes. -/
theorem dpre_of {s : State} (h : decRVC.pre s) : DPre s := by
  obtain ⟨⟨hrd, hwr, hpo, hpw, how, hfo, hfp, hfs, hal⟩, hc⟩ := h
  have hc' : ConstsOk [(sqrtSym, sqrtWords)] 0 s := hc
  have hl := sqrtWords_length
  have hr := hc'.rd1
  have hw := hc'.wr1
  have hf := hc'.fit (List.mem_cons_self)
  rw [hl] at hr hw hf
  have hrd' : s.rd = [⟨s.gpr .a1, 29⟩, ⟨s.syms sqrtSym, 12288⟩] := by
    have e1 : s.rd.drop (s.rd.length - 1) = [⟨s.syms sqrtSym, 8 * sqrtWords.length⟩] := hc'.1
    rw [hl] at e1
    have e0 : s.rd.take (s.rd.length - 1) = [⟨s.gpr .a1, 29⟩] := hrd
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e0, e1]; rfl
  have hwr' : s.wr = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a2, 8192⟩] := hwr
  have hd : Region.Disjoint ⟨s.syms sqrtSym, 12288⟩ ⟨s.gpr .a2, 8192⟩ := hw _ (by rw [hwr']; simp)
  refine ⟨hrd', hwr, hpo, hpw, how, hfo, hfp, hfs, hal, ?_⟩
  refine ⟨fun i hi => hc'.held1 i (by rw [hl]; exact hi), hc'.aligned List.mem_cons_self,
    by rw [hrd']; simp, hf, fun d hd' => ?_⟩
  have hcn : (⟨s.syms sqrtSym, 12288⟩ : Region).Contains (s.syms sqrtSym + BitVec.ofNat 64 d) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have := hd _ hcn
  simp only [Region.Contains, Nat.not_le] at this
  simp only [VG.Proof.Mont.ofs]; omega

/-! ## Decompression's constant time, relating two runs -/

/-- Both runs satisfy `Φ a`, for the same `a`, with the same stack pointer. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

/-- `Φ a` fixes the registers `rs` and the table's address. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ s₁.syms sqrtSym = s₂.syms sqrtSym

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint (taintSym [sqrtSym]).T}
    (h : ((taintSym [sqrtSym]).check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taintSym [sqrtSym]) (Taint.ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨⟨hsp, fun r hr => (hpin a _ _ h₁ h₂).1 r (Taint.mem_ofRegs.mp hr)⟩,
      fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact (hpin a _ _ h₁ h₂).2⟩) h

/-- The public data of a run: the pointers, the table's address and `rhs`. -/
structure DA where
  out : Addr
  pk : Addr
  base : Addr
  T : Addr
  A : Spec.Weierstrass.Fe W

/-- On entry. -/
def Φ0 (a : DA) (s : State) : Prop :=
  DPre s ∧ s.gpr .a0 = a.out ∧ s.gpr .a1 = a.pk ∧ s.gpr .a2 = a.base ∧ s.syms sqrtSym = a.T ∧ rhsOf s = a.A

/-- After `j` digits. -/
def Φd (j : Nat) (a : DA) (s : State) : Prop :=
  ∃ s₀, s₀.gpr .s2 = a.out ∧ FSt a.A a.base s₀ ∧ DSt a.A a.base a.T s₀ s j

theorem pins_Φ0 : Pins Φ0 [.a0, .a1, .a2] := by
  rintro a s₁ s₂ ⟨-, a0, a1, a2, sy, -⟩ ⟨-, b0, b1, b2, sy', -⟩
  refine ⟨fun r hr => ?_, by rw [sy, sy']⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]

theorem pins_Φd (j : Nat) : Pins (Φd j) [.s0, .s4, .s5] := by
  rintro a s₁ s₂ ⟨_, _, _, D₁⟩ ⟨_, _, _, D₂⟩
  refine ⟨fun r hr => ?_, by rw [D₁.sym, D₂.sym]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [D₁.ws.s0, D₂.ws.s0]
  · rw [D₁.k.1, D₂.k.1]
  · rw [D₁.k.2, D₂.k.2]

theorem pins_tail : Pins (Φd 24) [.s0, .s2, .s4, .s5] := by
  rintro a s₁ s₂ ⟨_, h₁, _, D₁⟩ ⟨_, h₂, _, D₂⟩
  refine ⟨fun r hr => ?_, by rw [D₁.sym, D₂.sym]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [D₁.ws.s0, D₂.ws.s0]
  · rw [D₁.ks.gpr _ (by decide) (by decide), D₂.ks.gpr _ (by decide) (by decide), h₁, h₂]
  · rw [D₁.k.1, D₂.k.1]
  · rw [D₁.k.2, D₂.k.2]

theorem front_rel : RelCT isa (Two Φ0) front224 (Two (Φd 0)) :=
  two_post (two_taint _ pins_Φ0 (by taint_decide)) fun a s ⟨hs, h0, _, h2, hT, hA⟩ =>
    WP.mono (front_ok hs) fun s' F => ⟨s', by rw [F.s2, h0], by rw [← hA, ← h2]; exact F.fst,
      by rw [← hA, ← h2, ← hT]; exact F.dst⟩

/-- Each digit is checked by the taint analysis from the registers of the digits. -/
theorem digit_ct (j : Nat) (hj : j < 24) :
    ∃ hc, ((taintSym [sqrtSym]).check (Taint.ofRegs [.s0, .s4, .s5]) (digit j) hc).isSome = true := by
  match j, hj with
  | 0, _ => exact ⟨_, by taint_decide⟩
  | 1, _ => exact ⟨_, by taint_decide⟩
  | 2, _ => exact ⟨_, by taint_decide⟩
  | 3, _ => exact ⟨_, by taint_decide⟩
  | 4, _ => exact ⟨_, by taint_decide⟩
  | 5, _ => exact ⟨_, by taint_decide⟩
  | 6, _ => exact ⟨_, by taint_decide⟩
  | 7, _ => exact ⟨_, by taint_decide⟩
  | 8, _ => exact ⟨_, by taint_decide⟩
  | 9, _ => exact ⟨_, by taint_decide⟩
  | 10, _ => exact ⟨_, by taint_decide⟩
  | 11, _ => exact ⟨_, by taint_decide⟩
  | 12, _ => exact ⟨_, by taint_decide⟩
  | 13, _ => exact ⟨_, by taint_decide⟩
  | 14, _ => exact ⟨_, by taint_decide⟩
  | 15, _ => exact ⟨_, by taint_decide⟩
  | 16, _ => exact ⟨_, by taint_decide⟩
  | 17, _ => exact ⟨_, by taint_decide⟩
  | 18, _ => exact ⟨_, by taint_decide⟩
  | 19, _ => exact ⟨_, by taint_decide⟩
  | 20, _ => exact ⟨_, by taint_decide⟩
  | 21, _ => exact ⟨_, by taint_decide⟩
  | 22, _ => exact ⟨_, by taint_decide⟩
  | 23, _ => exact ⟨_, by taint_decide⟩
  | _ + 24, h => exact absurd h (by omega)

theorem digits_rel : ∀ j, j ≤ 24 → RelCT isa (Two (Φd 0)) (digits j) (Two (Φd j))
  | 0, _ => by
    rw [digits]
    exact two_post (two_taint [.s0, .s4, .s5] (pins_Φd 0) (hc := .block [] 1024) rfl) fun _ _ h => WP.block_nil h
  | j + 1, hj => by
    rw [digits]
    obtain ⟨hc, h⟩ := digit_ct j (by omega)
    exact RelCT.seq (digits_rel j (by omega)) (two_post (two_taint _ (pins_Φd j) h)
      fun a s ⟨s₀, h2, F, D⟩ => WP.mono (digit_ok (by omega) F D) fun s' D' => ⟨s₀, h2, F, D'⟩)

theorem tail_ct : RelCT isa (Two (Φd 24)) tail224 fun _ _ => True :=
  two_taint _ pins_tail (by taint_decide)


/-- Equal bytes of the public key give equal `rhs`. -/
theorem rhsOf_eq {s₁ s₂ : State}
    (h : (Spec.EcKey.bytesAt s₁.mem (s₁.gpr .a1) 29).map (·.toNat) =
      (Spec.EcKey.bytesAt s₂.mem (s₂.gpr .a1) 29).map (·.toNat)) : rhsOf s₂ = rhsOf s₁ := by
  have hb' : Spec.EcKey.bytesAt s₁.mem (s₁.gpr .a1) 29 = Spec.EcKey.bytesAt s₂.mem (s₂.gpr .a1) 29 :=
    (List.map_inj_right fun x y h => BitVec.eq_of_toNat_eq h).mp h
  have hb : Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .a1) 29 = Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .a1) 29 := hb'
  have hd : ∀ t : State, Spec.Ecdsa.bytesAt t.mem (t.gpr .a1 + BitVec.ofNat 64 1) 28 =
      (Spec.Ecdsa.bytesAt t.mem (t.gpr .a1) 29).drop 1 := fun t => by
    rw [show (29 : Nat) = 1 + 28 from rfl, VG.Proof.Weierstrass.bytesAt_add,
      List.drop_left' (VG.Proof.Weierstrass.length_bytesAt _ _ _)]
  unfold rhsOf
  rw [hd s₂, hd s₁, hb]

theorem decompress_rel : RelCT isa (Two Φ0) decompressP224 fun _ _ => True :=
  RelCT.seq front_rel (RelCT.seq (digits_rel 24 (Nat.le_refl _)) tail_ct)

theorem decompress_ct : ConstantTime isa decRVC.pre decRVC.pub decompressP224 :=
  RelCT.constantTime (decompress_rel.mono (fun s₁ _ ⟨h₁, h₂, ⟨hsp, h0, h1, h2, hb⟩, hsy⟩ =>
    ⟨⟨s₁.gpr .a0, s₁.gpr .a1, s₁.gpr .a2, s₁.syms sqrtSym, rhsOf s₁⟩, ⟨dpre_of h₁, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨dpre_of h₂, h0.symm, h1.symm, h2.symm, hsy.symm, rhsOf_eq hb⟩, hsp⟩) fun _ _ h => h)

theorem decompress_rv (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) (s : State) (hs : decRVC.pre s) :
    ∃ t s', Exec isa decompressP224 s t s' ∧ abiPreserved s s' ∧ decRVC.post s s' := by
  obtain ⟨t, s', he, h⟩ := decompress_ok hL (dpre_of hs)
  exact ⟨t, s', he, h⟩

theorem decRV_implies : decRV.Implies (Spec.EcKey.P224.inst.decompressPublicKeyContract RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs]
        rcases (h : DPostC s s') with ⟨h1, Q, hm, hb⟩ | ⟨h1, hn, hb⟩
        · exact Or.inl ⟨by rw [h1]; rfl, Q, hm, hb⟩
        · exact Or.inr ⟨by rw [h1]; rfl, hn, hb⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
          Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, decRV, DPre0,
          RISCV64.abi, RISCV64.argRegs, convSat] [convSat] using (convSat 57 29) }

/-- A memory holding the table at `0x100000`, for the witness of the contract
with it (irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def sqrtSatMem : Mem := constMem 0x100000 sqrtWords

theorem sqrtSatMem_held : ∀ i < sqrtWords.length,
    sqrtSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = sqrtWords.getD i 0 := by
  have h := constMem_held 0x100000 sqrtWords (by rw [sqrtWords_length]; decide)
  unfold sqrtSatMem
  exact h

/-- A state satisfying the precondition with the table. -/
def decSatC : State :=
  { convSat 57 29 with mem := sqrtSatMem, rd := (convSat 57 29).rd ++ [⟨0x100000, 12288⟩], syms := fun _ => 0x100000 }

theorem dec_sat : (Spec.EcKey.P224.inst.decompressPublicKeyContract (RISCV64.abi.withConsts sqrtConsts)).pre decSatC := by
  have hl := sqrtWords_length
  have held := sqrtSatMem_held
  rw [show sqrtConsts = [(sqrtSym, sqrtWords)] from rfl]
  generalize sqrtWords = W' at hl held ⊢
  generalize e : decSatC = s
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, RISCV64.abi,
    RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem decRVC_implies :
    decRVC.Implies (Spec.EcKey.P224.inst.decompressPublicKeyContract (RISCV64.abi.withConsts sqrtConsts)) :=
  { pre := fun _ hs => ⟨decRV_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr (decRV_implies.post (stripConsts _ s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨decRV_implies.pub (stripConsts _ s₁) (stripConsts _ s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨decSatC, dec_sat⟩ }

theorem decompress_verified (hL : VG.Proof.Weierstrass.Law Spec.P224.curve) :
    Verified RISCV64.target decompressP224
      (Spec.EcKey.P224.inst.decompressPublicKeyContract (RISCV64.abi.withConsts sqrtConsts)) :=
  Verified.of_correct (decompress_rv hL) decompress_ct decRVC_implies

end VG.Proof.EcKey.Compressed.RISCV64.P224
