module

public import VerifiedGarbage.Proof.MlKem.X86_64.EcBase
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes

/-!
# ML-KEM on x86-64: encapsulation hashing the key, its contract, layout and entry

For a parameter set `L`: the contract the proof of `kemEncaps`
(`Impl/MlKem/X86_64/Encaps.lean`) is written against (`encK L`, which the
shared contract implies), and what holds throughout (`EK`: `Top`, and `ek`
and `m` at their pointers). The function keeps its buffers in the registers
`kemEncapsH` keeps them in, so its layout (`ecR`, `ecW`) and the checks of
`EcWfB L` are those of `EcBase.lean`; only the entry differs (no `h`, and the
other pointers one register earlier: `ekM`). Then the prologue (`pro_ok`),
`H(ek)` with the sponge functions (`hashEk_ok`) and `G(m ‖ H(ek))`
(`hashes_ok`), and the context `K-PKE.Encrypt` runs in (`ekC`, which also
keeps `K`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemEncaps L (ek = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8) -> eax`, with 32 bytes of stack. -/
def encK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, L.ekLen⟩, ⟨s.gpr .rsi, 32⟩] ∧
    s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.ctLen⟩, ⟨s.gpr .r8, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .r8, L.scr⟩ ∧
    (s.gpr .rdi).toNat + L.ekLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.ctLen ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => encapsInternal L.p iters (bytesAt s.mem (s.gpr .rdi) L.ekLen)
      (bytesAt s.mem (s.gpr .rsi) 32)) ((s'.gpr .rax).setWidth 32)
      (bytesAt s'.mem (s.gpr .rdx) 32, bytesAt s'.mem (s.gpr .rcx) L.ctLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    ekRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) L.ekLen) = ekRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) L.ekLen)

namespace Ek

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk eckChk EcWfB hW₃)

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev ekM : List (Reg × Reg) := [(.rbx, .r8), (.rbp, .rsi), (.r12, .rdx), (.r13, .rcx), (.r14, .rdi)]

theorem ekM_bases : ∀ p ∈ ekM, p.1 ∈ bases := by decide

section
variable {L : Kem} {σ : State}

/-- The layout of encapsulation. -/
theorem ekLay (W : EcWfB L) (hp : (encK L).pre σ) {s : State} (h : Top ekM σ s) : Lay (ecR L) (ecW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5,
    n1, n2, n3, n4, n5⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rsi := h.regs (.rbp, .rsi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rcx := h.regs (.r13, .rcx) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rdi := h.regs (.r14, .rdi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_)
    (fa5 ?_ ?_ ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, e5, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d6
  · exact fun _ => d4
  · exact fun _ => d5
  · exact fun _ => d8.symm
  · exact fun _ => d9.symm
  · exact fun _ => d7
  exacts [k1, k2, k5, k3, k4, n1, n2, n5, n3, n4,
    mem ⟨σ.gpr .rdi, L.ekLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, 32⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .r8, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rcx, L.ctLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r2, r5, r3, r4]

end

/-- `ek`, `m`, and `G(m ‖ H(ek))`. -/
abbrev ekE (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) L.ekLen
abbrev ekMs (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 32
abbrev ekG (L : Kem) (σ : State) : List Byte × List Byte := G (ekMs σ ++ H (ekE L σ))

/-- What holds throughout. -/
structure EK (L : Kem) (σ s : State) : Prop where
  top : Top ekM σ s
  ek : bytesAt s.mem (pa s (.r14, 0)) L.ekLen = ekE L σ
  m : bytesAt s.mem (pa s (.rbp, 0)) 32 = ekMs σ

section
variable {L : Kem} (W : EcWfB L) {σ : State} (hp : (encK L).pre σ)
include W hp

theorem EK.lay {s : State} (h : EK L σ s) : Lay (ecR L) (ecW L) s := ekLay W hp h.top

theorem EK.step {s s' : State} (h : EK L σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : ecChk L ws = true) : EK L σ s' := by
  simp only [Encaps.ecChk, Bool.and_eq_true] at hc
  have L₀ := h.lay W hp
  exact ⟨h.top.step L₀ hP ekM_bases hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.ek,
    by rw [L₀.keepBytes hP hc.2]; exact h.m⟩

end

/-- What `K-PKE.Encrypt` keeps: `EK`, and `K` at `G`. -/
structure EKK (L : Kem) (σ s : State) : Prop where
  ec : EK L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (ekG L σ).1

theorem EKK.step {L : Kem} (W : EcWfB L) {σ : State} (hp : (encK L).pre σ) {s s' : State} (h : EKK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : eckChk L ws = true) : EKK L σ s' := by
  simp only [Encaps.eckChk, Bool.and_eq_true] at hc
  exact ⟨h.ec.step W hp hP hc.1, by rw [(h.ec.lay W hp).keepBytes hP hc.2]; exact h.k⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def ekC {L : Kem} (W : EcWfB L) (σ : State) : Ctx (ecR L) (ecW L) where
  Out s := (encK L).pre σ ∧ EKK L σ s
  chk := eckChk L
  bs := ecB_bases L
  lay h := h.2.ec.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def ekCA {L : Kem} (W : EcWfB L) : Ctx (ecR L) (ecW L) where
  Out s := ∃ σ, (encK L).pre σ ∧ EKK L σ s
  chk := eckChk L
  bs := ecB_bases L
  lay := fun ⟨_, hp, h⟩ => h.ec.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

theorem pro_eq : Encaps.pro = [.store (at_ .r8 840) .rbx, .store (at_ .r8 848) .rbp, .store (at_ .r8 856) .r12,
    .store (at_ .r8 864) .r13, .store (at_ .r8 872) .r14, .store (at_ .r8 880) .r15, .mov .rbx (.reg .r8),
    .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rcx), .mov .r14 (.reg .rdi),
    .mov32 .r15 (.imm 1)] := rfl

/-- After the prologue: `EK`, and `r15 = 1`. -/
structure ProOut (L : Kem) (σ s : State) : Prop where
  ec : EK L σ s
  r15 : s.gpr .r15 = 1

theorem pro_ok {L : Kem} (W : EcWfB L) {σ : State} (hp : (encK L).pre σ) :
    WP isa (.block Encaps.pro) σ (ProOut L σ) := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5,
    n1, n2, n3, n4, n5⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .r8, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .r8, L.scr⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧ s.gpr .r13 = σ.gpr .rcx ∧
    s.gpr .r14 = σ.gpr .rdi ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r8, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have hek := W.small (.r14, L.ekLen) (by simp)
  refine ⟨⟨⟨k.2.1, k.2.2, hsp, fa5 hbx hbp h12 h13 h14, fun j hj => ?_, ?_⟩, ?_, ?_⟩, h15⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d3) (by simp only at hek; omega)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d6) (by decide)

/-! ## `G(m ‖ H(ek))` -/

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI {L : Kem} (W : EcWfB L) (σ s : State) : Prop :=
  Enc.EIn L (ekC W σ) (.r14, 0) (ekE L σ) (ekMs σ) (ekG L σ).2 s ∧ s.gpr .r15 = 1

/-- `m` to `M`, and `G(m ‖ H(ek))`, with `H(ek)` at `H`: what it writes, `r15`, and the inputs of
`K-PKE.Encrypt`. -/
theorem hashes_okP {L : Kem} (W : EcWfB L) {σ : State} (hp : (encK L).pre σ) {s : State}
    (h : EK L σ s) (hH : bytesAt s.mem (pa s (sc oH)) 32 = H (ekE L σ)) :
    WP isa EncapsH.hashes s fun s' => PPostB s s' ([(sc oM, 32)] ++ hW₃) ∧ s'.gpr .r15 = s.gpr .r15 ∧
      Enc.EIn L (ekC W σ) (.r14, 0) (ekE L σ) (ekMs σ) (ekG L σ).2 s' := by
  have L₀ := h.lay W hp
  unfold EncapsH.hashes
  refine WP.seq (WP.mono (copy_okL L₀ (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) W.h₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  rw [h.m] at hb₁
  have hH₁ : bytesAt s₁.mem (pa s₁ (sc oH)) 32 = H (ekE L σ) := by rw [L₀.keepBytes hP₁.b W.h₁H, hH]
  refine WP.mono (hash_ok (ecB_bases L) (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64)
    W.h₃ (show 6 < 256 by decide) L₁) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have k₃ := k₁.step W hp hP₃.b W.h₃K
  rw [← hP₁.pa rbx_cs] at hb₁
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hb₁, hH₁, KeyGen.sha3Suffix6] at hb₃
  rw [← sha3_512_eq, ← hP₃.pa rbx_cs] at hb₃
  have hK : bytesAt s₃.mem (pa s₃ (sc oG)) 32 = (ekG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₃]; rfl
  have hr : bytesAt s₃.mem (pa s₃ sigP) 32 = (ekG L σ).2 := by
    have e := bytesAt_drop s₃.mem (pa s₃ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₃.mem (pa s₃ (sc oG)) 64).drop 32 = bytesAt s₃.mem (pa s₃ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₃]; rfl
  refine ⟨PPostB.app hP₁.b hP₃.b (by decide), by rw [hP₃.cs .r15 (by decide), hP₁.cs .r15 (by decide)],
    ⟨hp, k₃, hK⟩, k₃.ek, ?_, hr⟩
  rw [L₁.keepBytes hP₃.b W.h₃M, hb₁]

/-- `m` to `M`, and `G(m ‖ H(ek))`, with `H(ek)` at `H`. -/
theorem hashes_ok {L : Kem} (W : EcWfB L) {σ : State} (hp : (encK L).pre σ) {s : State}
    (h : EK L σ s) (hH : bytesAt s.mem (pa s (sc oH)) 32 = H (ekE L σ)) (h15 : s.gpr .r15 = 1) :
    WP isa EncapsH.hashes s (EncI W σ) :=
  WP.mono (hashes_okP W hp h hH) fun _ ⟨_, e, hi⟩ => ⟨hi, by rw [e, h15]⟩

end Ek

end VG.Proof.MlKem.X86_64
