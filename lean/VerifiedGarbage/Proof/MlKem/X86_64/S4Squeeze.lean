module

public import VerifiedGarbage.Proof.Sha3.Seed34
public import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base
import VerifiedGarbage.Proof.Sha3.X86_64.Permute

/-! ### `MlKem.X86_64.S4Absorb`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the round constants and the padded seeds

After the prologue, the table of the round constants (`rc_ok`), and the four
states holding the padded seeds, byte by byte (`absorb_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.Sha3.X86_64.X4 (q4 VUpd la ba Lanes4 wp_vmovq wp_vbcast wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.Sha3.X86_64 (wp_movi64)

/-- `Env` after writes below the saved registers. -/
theorem EnvW.write {σ s s' : State} (he : EnvW w16 σ s) {a n : Nat} (h : a + n ≤ oSave)
    (hf : Frame [⟨at' σ a, n⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : EnvW w16 σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using Offset.disjoint (scr σ) (d := oSave + 8 * i) (n := 8) (e := a) (k := n) (by simp only [oSave] at h ⊢; omega_using [h])
          (by simp only [oSave]; omega_using [hi]) (by simp only [oSave] at h; omega_using [h])) (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR σ, by simp, Offset.sub_base _ (by simp only [oSave] at h; omega_using [h])⟩

/-! ## Bytes written -/

/-- A byte of a write at `p + e`. -/
theorem wb_in (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {e d : Nat} (h₁ : e ≤ d) (h₂ : 8 * (d - e + 1) ≤ w)
    (hw : w < 2 ^ 64) : (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 d) = v.extractLsb' (8 * (d - e)) 8 := by
  rw [← writeW_byte m _ v h₂ hw, Offset.add_add, Nat.add_sub_cancel' h₁]

/-- A byte outside a write at `p + e`. -/
theorem wb_out (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {e d : Nat} (h : d < e ∨ e + w / 8 ≤ d)
    (hd : d < 2 ^ 63) (he : e + w / 8 < 2 ^ 63) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 d) = m (p + BitVec.ofNat 64 d) := by
  refine writeW_byte_off _ _ _ _ ?_
  rw [Offset.sub_toNat' _ (by bdd_omega) (by bdd_omega)]
  split <;> omega_arith

/-! ## The round constants -/

/-- After the first `n` round constants. -/
structure RcInvW (w16 : Bool) (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [⟨at' σ oRc, 768⟩] s₀.mem s.mem
  rc : ∀ r < n, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = Spec.Sha3.RC r

theorem rc_step {σ : State} (hp : PreW w16 σ) {s₀ : State} (he : EnvW w16 σ s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : RcInvW w16 σ s₀ r s) :
    WP isa (.block [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0]) s
      (RcInvW w16 σ s₀ (r + 1)) := by
  have hbx : s.gpr .rbx = scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := at' σ (32 * (50 + r))) (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; rfl)
      (by rw [u₃.wr, u₂.wr, u₁.wr, h.keep.2.2, he.wr]; exact in_scr hp rfl (by bdd_omega))
      fun s₄ g₄ _ m₄ r₄ w₄ => VG.Proof.Sha3.X86_64.wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = Spec.Sha3.RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (at' σ (32 * (50 + r))) (s₃.ymm .xmm0) := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (by simpa using hg), h.keep.gpr hg],
      by rw [r₄, u₃.rd, u₂.rd, u₁.rd, h.keep.2.1], by rw [w₄, u₃.wr, u₂.wr, u₁.wr, h.keep.2.2]⟩, ?_,
    fun r' hr' k hk => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [oRc]; omega_using [])
      (by simp only [oRc]; omega_using [hr]) (by simp only [oRc]; omega_using []))
  · rw [hm]
    by_cases e : r' = r
    · subst e
      rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
    · have e := readW_writeW_off s.mem (scr σ) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
        (e := 32 * (50 + r)) (n := 8) (by bdd_omega) (by bdd_omega) (by bdd_omega)
      exact e.trans (h.rc r' (by bdd_omega) k hk)

theorem rcTable_eq : Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0] := rfl

/-- The table of the round constants. -/
theorem rc_ok {σ : State} (hp : PreW w16 σ) {s₀ : State} (he : EnvW w16 σ s₀) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32))) s₀ (RcInvW w16 σ s₀ 24) := by
  rw [rcTable_eq]
  exact wp_range_flatMap (M := isa) (RcInvW w16 σ s₀) (fun r s hr h => rc_step hp he hr h) 24 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by bdd_omega)⟩

/-! ## The states, byte by byte -/

/-- The offset of byte `q` of state `k`. -/
abbrev off4 (k q : Nat) : Nat := 32 * (q / 8) + 8 * k + q % 8

/-- The bytes of the states after a write at `p + e`. -/
theorem bytes_write {m : Mem} {p : Addr} {F : Nat → Nat → Byte}
    (h : ∀ k < 4, ∀ q < 200, m (ba p k q) = F k q) {w : Nat} (v : BitVec w) {e : Nat} (hw : w < 2 ^ 64)
    (he : e + w / 8 < 2 ^ 62) {k q : Nat} (hk : k < 4) (hq : q < 200) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (ba p k q) =
      if e ≤ off4 k q ∧ off4 k q < e + w / 8 then v.extractLsb' (8 * (off4 k q - e)) 8 else F k q := by
  split
  · rename_i hc
    simp only [off4] at hc
    exact wb_in m p v hc.1 (by bdd_omega) hw
  · rename_i hc
    simp only [off4] at hc
    rw [ba, wb_out m p v (by bdd_omega) (by bdd_omega) (by bdd_omega)]
    exact h k hk q hq

/-- The four states hold `F`. -/
def SB (σ : State) (m : Mem) (F : Nat → Nat → Byte) : Prop :=
  ∀ k < 4, ∀ q < 200, m (ba (scr σ) k q) = F k q

/-- During the writes to the states, after the round constants (in `m₁`). -/
structure AIW (w16 : Bool) (σ : State) (m₁ : Mem) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  frame : Frame [⟨scr σ, 800⟩] m₁ s.mem

theorem AIW.write {σ : State} {m₁ : Mem} {s s' : State} (h : AIW w16 σ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    (hm : ∃ v : BitVec (8 * n), s'.mem = s.mem.writeW (at' σ e) v) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) : AIW w16 σ m₁ s' := by
  obtain ⟨v, hv⟩ := hm
  have hf : Frame [⟨at' σ e, n⟩] s.mem s'.mem := by
    rw [hv]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [show 8 * n / 8 = n by bdd_omega]; exact Region.contains_self _ _)
  refine ⟨h.env.write (by simp only [oSave]; omega_using [hn]) hf hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide), h.r14], h.frame.trans (hf.sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hn⟩

/-! ### Zeroing -/

/-- After zeroing the first `n` lanes of each state. -/
structure ZInvW (w16 : Bool) (σ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : AIW w16 σ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (scr σ) k q) = 0

theorem zero_step {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {i : Nat} (hi : i < 25) {s : State} (h : ZInvW w16 σ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx i .xmm0]) s (ZInvW w16 σ m₁ (i + 1)) := by
  refine wp_vst (a := at' σ (32 * i)) (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx])
    (by rw [h.ai.env.wr]; exact in_scr hp rfl (by bdd_omega)) fun s' g' q' m' r' w' => VG.Proof.Sha3.X86_64.wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by bdd_omega) ⟨_, m'⟩ r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := bytes_write (m := s.mem) (p := scr σ) (F := fun k q => s.mem (ba (scr σ) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by bdd_omega) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by bdd_omega, ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by bdd_omega),
      q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [off4] at hc
    exact h.bytes k hk q hq (by bdd_omega)

theorem zero4_eq : zero4 = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx i .xmm0] := rfl

theorem zero_ok {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {s : State} (h : AIW w16 σ m₁ s) :
    WP isa (.block zero4) s (fun s' => AIW w16 σ m₁ s' ∧ SB σ s'.mem fun _ _ => 0) := by
  rw [zero4_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (ZInvW w16 σ m₁) (fun i s hi h => zero_step hp hi h)
    25 (Nat.le_refl _) s₁ ⟨h.write (e := 0) (n := 0) (by bdd_omega) ⟨0, ?_⟩ u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by bdd_omega)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by bdd_omega)⟩
  rw [u₁.mem]
  funext x
  simp [Mem.writeW, Mem.write]

/-! ### The seeds -/

/-- Byte `q` of seed `k` (0 past its end). -/
abbrev Bq (σ : State) (k q : Nat) : Byte := (B σ k).getD q 0

/-- The states after the first `K` seeds, and the first `i` lanes of seed `K`. -/
def HF (σ : State) (K i : Nat) (k q : Nat) : Byte :=
  if (k < K ∧ q < 34) ∨ (k = K ∧ q < 8 * i) then Bq σ k q else 0

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
theorem lane_step {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {K i : Nat} (hK : K < 4) (hi : i < 4) {s : State}
    (h : AIW w16 σ m₁ s ∧ SB σ s.mem (HF σ K i)) :
    WP isa (.block [.mov .rax (.mem (at_ .r12 (34 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) s
      (fun s' => AIW w16 σ m₁ s' ∧ SB σ s'.mem (HF σ K (i + 1))) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := sd σ + BitVec.ofNat 64 (34 * K + 8 * i)) (by rw [ea_at, ha.env.r12])
    (in_sd' hp ha.env.rd ha.env.wr (by bdd_omega)) fun s₁ u₁ => wp_store (a := at' σ (32 * i + 8 * K))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact in_scr hp ha.env.wr (by bdd_omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (32 * i + 8 * K)) (s.mem.readW (sd σ + BitVec.ofNat 64 (34 * K + 8 * i)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨ha.write (e := 32 * i + 8 * K) (n := 8) (by bdd_omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [off4]
  by_cases hc : 32 * i + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * i + 8 * K + 64 / 8
  · have hk' : k = K := by bdd_omega
    have hq' : q / 8 = i := by bdd_omega
    subst hk'
    rw [ifp hc, HF, ifp (.inr ⟨rfl, by bdd_omega⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * i + 8 * k)) = 8 * (q % 8) by bdd_omega,
      byte_readW _ _ (by bdd_omega), Offset.add_add, show 34 * k + 8 * i + q % 8 = 34 * k + q by bdd_omega,
      seed_byte hp ha.env.frame hK (by bdd_omega)]
  · rw [ifn hc, HF, HF]
    by_cases hc' : (k < K ∧ q < 34) ∨ (k = K ∧ q < 8 * i)
    · rw [ifp hc', ifp (by bdd_omega)]
    · rw [ifn hc', ifn (by bdd_omega)]

theorem byte_setWidth (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 b) = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
/-- Byte `32 + j` of seed `K`. -/
theorem byte_step {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {K j : Nat} (hK : K < 4) (hj : j < 2) {s : State}
    (h : AIW w16 σ m₁ s ∧ SB σ s.mem fun k q => if (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + j) then Bq σ k q else 0) :
    WP isa (.block [.movzx8 .rax (at_ .r12 (34 * K + (32 + j))), .store8 (at_ .rbx (128 + 8 * K + j)) .rax]) s
      (fun s' => AIW w16 σ m₁ s' ∧
        SB σ s'.mem fun k q => if (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + (j + 1)) then Bq σ k q else 0) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movzx8 (a := sd σ + BitVec.ofNat 64 (34 * K + (32 + j))) (by rw [ea_at, ha.env.r12])
    (in_sd' hp ha.env.rd ha.env.wr (by bdd_omega)) fun s₁ u₁ => wp_store8 (a := at' σ (128 + 8 * K + j))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact in_scr hp ha.env.wr (by bdd_omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (128 + 8 * K + j)) (s.mem (sd σ + BitVec.ofNat 64 (34 * K + (32 + j)))) := by
    rw [m₂, u₁.mem, u₁.gpr, byte_setWidth]
  refine ⟨ha.write (e := 128 + 8 * K + j) (n := 1) (by bdd_omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [off4]
  by_cases hc : 128 + 8 * K + j ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 128 + 8 * K + j + 8 / 8
  · have hk' : k = K := by bdd_omega
    have hq' : q = 32 + j := by bdd_omega
    subst hk' hq'
    rw [ifp hc, ifp (.inr ⟨rfl, by bdd_omega⟩), show 8 * (32 * ((32 + j) / 8) + 8 * k + (32 + j) % 8 -
      (128 + 8 * k + j)) = 0 by bdd_omega, Proof.Sha3.extractLsb'_byte, seed_byte hp ha.env.frame hK (by bdd_omega)]
  · rw [ifn hc]
    by_cases hc' : (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + j)
    · rw [ifp hc', ifp (by bdd_omega)]
    · rw [ifn hc', ifn (by bdd_omega)]

theorem seedLanes_eq (K : Nat) : seedLanes K = (List.range 4).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (34 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) ++
    (([.movzx8 .rax (at_ .r12 (34 * K + (32 + 0))), .store8 (at_ .rbx (128 + 8 * K + 0)) .rax] : List Instr) ++
      ([.movzx8 .rax (at_ .r12 (34 * K + (32 + 1))), .store8 (at_ .rbx (128 + 8 * K + 1)) .rax] : List Instr)) := by
  simp only [seedLanes, Nat.add_zero]; rfl

/-- The states after the first `K` seeds. -/
def GF (σ : State) (K : Nat) (k q : Nat) : Byte := if k < K ∧ q < 34 then Bq σ k q else 0

theorem seed_step {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {K : Nat} (hK : K < 4) {s : State}
    (h : AIW w16 σ m₁ s ∧ SB σ s.mem (GF σ K)) :
    WP isa (.block (seedLanes K)) s (fun s' => AIW w16 σ m₁ s' ∧ SB σ s'.mem (GF σ (K + 1))) := by
  rw [seedLanes_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => AIW w16 σ m₁ s ∧ SB σ s.mem (HF σ K i))
    (fun i s hi h => lane_step hp hK hi h) 4 (Nat.le_refl _) s ⟨h.1, fun k hk q hq => ?_⟩) fun s₁ h₁ => ?_
  · rw [h.2 k hk q hq, GF, HF]
    by_cases hc : k < K ∧ q < 34
    · rw [ifp hc, ifp (.inl hc)]
    · rw [ifn hc, ifn (by bdd_omega)]
  rw [WP.block_append_iff]
  refine WP.mono (byte_step hp (j := 0) hK (by decide) ⟨h₁.1, fun k hk q hq => ?_⟩) fun s₂ h₂ =>
    WP.mono (byte_step hp (j := 1) hK (by decide) h₂) fun s₃ ⟨h₃, b₃⟩ => ⟨h₃, fun k hk q hq => ?_⟩
  · rw [h₁.2 k hk q hq, HF]
  · rw [b₃ k hk q hq, GF]
    dsimp only
    by_cases hc : (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + (1 + 1))
    · rw [ifp hc]
      by_cases hc' : k < K + 1 ∧ q < 34
      · rw [ifp hc']
      · rw [ifn hc']; omega
    · rw [ifn hc]
      by_cases hc' : k < K + 1 ∧ q < 34
      · omega
      · rw [ifn hc']

/-! ### The padding -/

open VG.Proof.Sha3.X86_64 (wp_store8 wp_mov32i wp_nil) in
/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4)
    (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : AIW w16 σ m₁ s ∧ SB σ s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => AIW w16 σ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        SB σ s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_store8 (a := at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) (by rw [ea_at, ha.env.rbx])
    (by exact in_scr hp ha.env.wr (by bdd_omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, byte_setWidth]
  refine ⟨ha.write (n := 1) (by bdd_omega) ⟨_, hm⟩ r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by bdd_omega
    rw [ifp hc, ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by bdd_omega,
      Proof.Sha3.extractLsb'_byte]
  · rw [ifn hc, ifn (by bdd_omega)]

/-- The four states hold their padded seeds. -/
def PF (σ : State) (k q : Nat) : Byte :=
  if q < 34 then Bq σ k q else if q = 34 then 0x1f else if q = 167 then 0x80 else 0

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200)
    {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : AIW w16 σ m₁ s ∧ SB σ s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => AIW w16 σ m₁ s' ∧ SB σ s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => AIW w16 σ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      SB σ s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, _, hb⟩ => ⟨ha, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [ifp e, ifp (by bdd_omega)]
    · rw [ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [ifp e', ifp (by bdd_omega)]
      · rw [ifn e', ifn (by bdd_omega)]
  · rw [h.2 k hk q hq]; dsimp only; rw [ifn (by bdd_omega)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [ifp e, ifp ⟨hk, e⟩]
    · rw [ifn e, ifn (by bdd_omega)]

theorem absorb4_eq : absorb4 = zero4 ++ ((List.range 4).flatMap seedLanes ++
    (([.mov32 .rax (.imm 0x1f)] : List Instr) ++ ((List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (34 / 8) + 8 * k + 34 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++ (List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (167 / 8) + 8 * k + 167 % 8)) .rax]))))) := by
  simp only [absorb4, List.append_assoc, List.cons_append, List.nil_append]

open VG.Proof.Sha3.X86_64 (wp_mov32i) in
/-- The padded seeds in the four states. -/
theorem absorb_ok {σ : State} (hp : PreW w16 σ) {m₁ : Mem} {s : State} (h : AIW w16 σ m₁ s) :
    WP isa (.block absorb4) s (fun s' => AIW w16 σ m₁ s' ∧ SB σ s'.mem (PF σ)) := by
  rw [absorb4_eq, WP.block_append_iff]
  refine WP.mono (zero_ok hp h) fun s₁ ⟨h₁, z₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => AIW w16 σ m₁ s ∧ SB σ s.mem (GF σ K))
    (fun K s hK h => seed_step hp hK h) 4 (Nat.le_refl _) s₁ ⟨h₁, fun k hk q hq => ?_⟩) fun s₂ h₂ => ?_
  · rw [z₁ k hk q hq, GF, ifn (by bdd_omega)]
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₃ => AIW w16 σ m₁ s₃ ∧ s₃.gpr .rax = (0x1f : Byte).setWidth 64 ∧ SB σ s₃.mem (GF σ 4))
    ⟨h₂.1.write (e := 0) (n := 0) (by bdd_omega) ⟨0, ?_⟩ u₃.rd u₃.wr fun r hr => u₃.other r hr, by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact h₂.2⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  · rw [u₃.mem]; funext x; simp [Mem.writeW, Mem.write]
  rw [WP.block_append_iff]
  refine WP.mono (cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, b₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₅ u₅ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₅ => AIW w16 σ m₁ s₅ ∧ s₅.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      SB σ s₅.mem fun k q => if q = 34 then 0x1f else GF σ 4 k q)
    ⟨a₄.write (e := 0) (n := 0) (by bdd_omega) ⟨0, ?_⟩ u₅.rd u₅.wr fun r hr => u₅.other r hr, by rw [u₅.gpr]; rfl,
      by rw [u₅.mem]; exact b₄⟩) fun s₅ ⟨a₅, x₅, b₅⟩ => ?_
  · rw [u₅.mem]; funext x; simp [Mem.writeW, Mem.write]
  refine WP.mono (cbytes_ok hp (by decide) x₅ ⟨a₅, b₅⟩) fun s₆ ⟨a₆, b₆⟩ => ⟨a₆, fun k hk q hq => ?_⟩
  rw [b₆ k hk q hq, PF]
  dsimp only
  rw [GF]
  by_cases e1 : q < 34
  · rw [ifn (show ¬ q = 167 by bdd_omega), ifn (show ¬ q = 34 by bdd_omega), ifp (show k < 4 ∧ q < 34 from ⟨hk, e1⟩),
      ifp e1]
  · rw [ifn e1, ifn (show ¬ (k < 4 ∧ q < 34) by bdd_omega)]
    by_cases e2 : q = 34
    · rw [ifn (show ¬ q = 167 by bdd_omega), ifp e2, ifp e2]
    · rw [ifn e2, ifn e2]

end VG.Proof.MlKem.X86_64.S4

end

end

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, squeezing

The padded seeds are the states that `Keccak-f` turns into the absorbed ones
(`padded_A0`), and the four states hold them after `absorb4` (`lanes_A0`).
Each `squeeze` permutes the four states (`permute4_ok`) and copies the
first 168 bytes of each to block `n` of its output, at `rbp`, which then
holds the first `168 (n + 1)` bytes of the seed's XOF output (`SqInvW`);
`squeezes` runs them in a loop (`blocks_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.S4

variable {w16 : Bool}

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (padded xofByte)
open VG.Proof.Sha3.X86_64.X4 (la ba Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok)

/-! ## The padded seeds -/

export VG.Proof.Sha3.Seed34 (A0 padded_A0 byteOf_A0 xofByte_A0)

theorem B_length (σ : State) (k : Nat) : (B σ k).length = 34 := VG.Proof.Sha3.bytesAt_length _ _ _

/-! ## `Env` after writes -/

/-- `Env` after writes below the saved registers. -/
theorem EnvW.low {σ s s' : State} (he : EnvW w16 σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨scr σ, oSave⟩)
    (hf : Frame rs s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : EnvW w16 σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Offset.base_disjoint (scr σ) (k := oSave)
        (e := oSave + 8 * i) (n := 8) (by omega_arith) (by simp only [oSave]; omega_arith)).symm).sub_right (hrs r hr))
      (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ⟨scrR σ, by simp, fun x hx => Offset.sub_base (scr σ) (d := 0)
      (n := oSave) (k := 8192) (by simp only [oSave]; omega_arith) x (by rw [BitVec.add_zero]; exact hrs r hr x hx)⟩)

/-- `Env` after code that writes no memory and keeps its registers. -/
theorem EnvW.keep {σ s s' : State} (he : EnvW w16 σ s) (hm : s'.mem = s.mem) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], r ∉ rs) : EnvW w16 σ s' :=
  EnvW.low he (rs := []) (by simp) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2 fun r hr => hk.gpr (hrs r hr)

/-! ## Loops of blocks -/

theorem sx_ofNat {x : Nat} (hx : x < 2 ^ 31) : (BitVec.ofNat 32 x).signExtend 64 = BitVec.ofNat 64 x := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
    omega_arith
  · rw [BitVec.msb_eq_decide]; simp; omega_arith

theorem cnt_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · simp only [hn, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp at this; omega_arith

theorem cnt_sub (n : Nat) (h₁ : 1 ≤ n) :
    BitVec.ofNat 64 n - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n - 1) := by
  rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h₁]

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

/-- In a loop of blocks: at block `i`, with `rbp` at `D + step (i - b)` and
`r10` the number of blocks left. -/
def BInv (P : Nat → State → Prop) (D : Addr) (step b n m : Nat) (s : State) : Prop :=
  ∃ i, b ≤ i ∧ i < b + n ∧ m = b + n - i ∧ P i s ∧ s.gpr .rbp = D + BitVec.ofNat 64 (step * (i - b)) ∧
    s.gpr .r10 = BitVec.ofNat 64 (b + n - i)

open VG.Proof.Sha3.X86_64 (wp_mov wp_addi wp_mov32i wp_subi wp_nil) in
/-- `blocks start step n body` from `P b`, where `P` does not depend on
`rbp`, `r10` or the flags, and `body` takes block `i` (with `rbp` at
`rbx + start + step (i - b)`) from `P i` to `P (i + 1)` and keeps `rbp`
and `r10`. -/
theorem blocks_ok {start step b n : Nat} {body : Prog isa} {P : Nat → State → Prop} {s : State}
    (hn : 0 < n) (hn' : n < 2 ^ 31) (hst : start < 2 ^ 31) (hsp : step < 2 ^ 31)
    (hP : ∀ i s s', P i s → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .rbp → r ≠ .r10 → s'.gpr r = s.gpr r) → P i s')
    (hbody : ∀ i t, b ≤ i → i < b + n → P i t →
      t.gpr .rbp = s.gpr .rbx + BitVec.ofNat 64 start + BitVec.ofNat 64 (step * (i - b)) →
      WP isa body t fun t' => P (i + 1) t' ∧ t'.gpr .rbp = t.gpr .rbp ∧ t'.gpr .r10 = t.gpr .r10)
    (h : P b s) : WP isa (blocks start step n body) s (P (b + n)) := by
  unfold blocks
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ => wp_nil ?_)
  refine WP.loop (M := isa) (BInv P (s.gpr .rbx + BitVec.ofNat 64 start) step b n) (fun m t ht => ?_) n s₃
    ⟨b, Nat.le_refl _, by omega_arith, by omega_arith, hP _ _ _ h (u₃.mem.trans (u₂.mem.trans u₁.mem))
      (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr))
      (fun r h₁ h₂ => (u₃.other r h₂).trans ((u₂.other r h₁).trans (u₁.other r h₁))), ?_, ?_⟩
  · obtain ⟨i, hb, hi, rfl, hPi, hbp, h10⟩ := ht
    refine WP.seq (WP.mono (hbody i t hb hi hPi hbp) fun t₁ ⟨hP₁, bp₁, r₁⟩ =>
      wp_addi fun t₂ u₂ => wp_subi fun t₃ u₃ z₃ => wp_nil ?_)
    have hP₃ : P (i + 1) t₃ := hP _ _ _ hP₁ (u₃.mem.trans u₂.mem) (u₃.rd.trans u₂.rd) (u₃.wr.trans u₂.wr)
      fun r h₁ h₂ => (u₃.other r h₂).trans (u₂.other r h₁)
    have c₃ : t₂.gpr .r10 - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (b + n - i - 1) := by
      rw [u₂.other _ (by decide), r₁, h10, cnt_sub _ (by omega_arith)]
    rw [eval_ne, z₃, c₃, cnt_zero (by omega_arith)]
    by_cases hl : b + n - i - 1 = 0
    · left
      refine ⟨by simp [hl], ?_⟩
      rw [show b + n = i + 1 by omega_arith]
      exact hP₃
    · right
      refine ⟨by simp [hl], b + n - (i + 1), by omega_arith, i + 1, by omega_arith, by omega_arith, rfl, hP₃, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr, bp₁, hbp, sx_ofNat hsp,
          BitVec.add_assoc (s.gpr .rbx + BitVec.ofNat 64 start), BitVec.ofNat_add_ofNat,
          show i + 1 - b = (i - b) + 1 by omega_arith, Nat.mul_succ]
      · rw [u₃.gpr, c₃, show b + n - i - 1 = b + n - (i + 1) by omega_arith]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, sx_ofNat hst, Nat.sub_self, Nat.mul_zero, add_ofNat_zero]
  · rw [u₃.gpr, show b + n - b = n by omega_arith]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith

/-! ## The squeezes -/

/-- After `n` squeezes. -/
structure SqInvW (w16 : Bool) (σ : State) (n : Nat) (s : State) : Prop where
  env : EnvW w16 σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) fun k => iterF n (A0 (B σ k))
  buf : ∀ k < 4, ∀ p < 168 * n, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p

/-- `SqInvW` with 32-bit coefficients. -/
abbrev SqInv := SqInvW false

theorem lanes_A0 {σ : State} {m : Mem} (h : SB σ m (PF σ)) : Lanes4 m (scr σ) fun k => iterF 0 (A0 (B σ k)) :=
  lanes4_of_bytes fun k hk q hq => by
    rw [h k hk q hq, show iterF 0 (A0 (B σ k)) = A0 (B σ k) from rfl, byteOf_A0 (B_length σ k) hq, PF]

theorem la_tbl (σ : State) (r k : Nat) : la (at' σ 1600) r k = la (scr σ) (50 + r) k := by
  rw [la, la, at', Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by omega_arith]

theorem sx800 : BitVec.signExtend 64 (BitVec.ofNat 32 oTmp) = BitVec.ofNat 64 800 := by decide
theorem sx1600 : BitVec.signExtend 64 (BitVec.ofNat 32 oRc) = BitVec.ofNat 64 1600 := by decide
theorem sx2368 : BitVec.signExtend 64 (BitVec.ofNat 32 oBuf) = BitVec.ofNat 64 2368 := by decide

theorem args_ok {σ s : State} (he : EnvW w16 σ s) :
    WP isa (.block permArgs) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = scr σ ∧ s'.gpr .rsi = at' σ 800 ∧
      s'.gpr .rdx = at' σ 1600 ∧ s'.gpr .rcx = at' σ 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold permArgs
  xrun [he.rbx, sx800, sx1600, sx2368]

/-- The permutation's precondition, in the scratch space. -/
theorem pre4 {σ : State} (hp : PreW w16 σ) {s : State} (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    (hrc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) :
    Pre4 s (scr σ) (at' σ 800) (at' σ 1600) :=
  ⟨fun i _ => in_scr hp hwr (a := 32 * i) (by omega_arith),
    fun i _ => by rw [at', Offset.add_add]; exact in_scr hp hwr (by omega_arith),
    fun r _ => by rw [at', Offset.add_add]; exact in_scr' hp hrd hwr (by omega_arith),
    Offset.base_disjoint _ (by omega_arith) (by omega_arith),
    Offset.base_disjoint _ (by omega_arith) (by omega_arith),
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith),
    fun r hr k hk => by rw [la_tbl]; exact hrc r hr k hk⟩

/-- A buffer byte, read through a frame of the states. -/
theorem buf_frame {σ : State} {m m' : Mem} {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' σ oBuf, 2016⟩ r) (hf : Frame rs m m') {k p : Nat} (hk : k < 4)
    (hp' : p < 504) : m' (at' σ (oBuf + 504 * k + p)) = m (at' σ (oBuf + 504 * k + p)) := by
  have := hf.bytes (R := ⟨at' σ oBuf, 2016⟩) hd (by simp only; omega_arith) (i := 504 * k + p) (by simp only; omega_arith)
  simpa only [at', Offset.add_add, Nat.add_assoc] using this

/-! ## Copying the output -/

theorem extract_eq : extract = (List.range 4).flatMap fun K => (List.range 21).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))), .store (at_ .rbp (504 * K + 8 * I)) .rax] := rfl

end VG.Proof.MlKem.X86_64.S4
