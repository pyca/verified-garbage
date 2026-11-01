module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.S2v
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesSiv.RISCV64.FinRaw
import VerifiedGarbage.Proof.CmacAes.RISCV64.Finalize

/-!
# AES-SIV on RISC-V: finishing S2V with a string shorter than a block

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, `shortTail` zeroes the tail at `W + 32`, copies `P` into it
(AES-CCM's `copy`, a byte at a time) and puts `0x80` after it, so the tail
is `pad(P)`, doubles `D` into `W + 272` a byte at a time and XORs it into
the tail (`shortTail_wp`); `shortMac` computes the CMAC of the tail, one
complete block, into `W + out` (`shortMac_wp`), which is S2V's end
(`Siv.s2vFinish_short`, `short_wp`). As on PPC64LE
(`Proof/AesSiv/PPC64LE/Short.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.CmacAes.Stream.RISCV64 (FArgs)
open VG.Proof.AesCcm.RISCV64 (BytesPre copy_wp copyRegs)
open VG.Spec.Aes (bytesAt)

/-- What S2V's end writes: `wR` and its result at `W + out`. -/
abbrev oR (c : Cx) (out : Nat) : List Region := ⟨c.W + BitVec.ofNat 64 out, 16⟩ :: wR c

theorem frame_oR {c : Cx} {m m' : Mem} (out : Nat) (h : Frame (wR c) m m') : Frame (oR c out) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem copyRegs_keep : ∀ r ∈ keepRegs, r ∉ copyRegs := by decide

theorem PK.ofKeeps {s t : State} (h : VG.Proof.AesCcm.RISCV64.Keeps s t) : PK s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (copyRegs_keep r hr)⟩

/-- The tail after the copy: `P` on zeros. -/
abbrev copiedMem (m : Mem) (W : Addr) (xs : List Byte) : Mem :=
  writeBytes (Proof.Cmac.zero2 m (W + BitVec.ofNat 64 tailO)) (W + BitVec.ofNat 64 tailO) xs

/-- `P` copied onto the zeroed tail (zeroed from `m₀`), if it is not empty. -/
theorem shortIte_wp {c : Cx} {s₁ : State} (E₁ : Env c s₁) {P : Addr} {n : Nat} (hP : Buf c s₁ P n)
    (hn : n < 16) (h19 : s₁.gpr .s6 = P) (h20₁ : s₁.gpr .s7 = BitVec.ofNat 64 n) {m₀ : Mem}
    (m₁ : s₁.mem = Proof.Cmac.zero2 m₀ (c.W + BitVec.ofNat 64 tailO)) (pmem : bytesAt s₁.mem P n = bytesAt m₀ P n) :
    WP isa (.ite (.zero .s7) (.block [])
        (.seq (.block [mov .a0 .s6, .addi .a1 .s1 (tailO : Int), mov .a2 .s7]) Impl.AesCcm.RISCV64.copy))
      s₁ fun s' => PK s₁ s' ∧ s'.gpr .s7 = s₁.gpr .s7 ∧
      s'.mem = copiedMem m₀ c.W (bytesAt m₀ P n) := by
  refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega) h20₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨PK.refl _, rfl, ?_⟩
    rw [m₁]; simp [bytesAt, writeBytes_nil]
  · have h0 : n ≠ 0 := by simpa using hf
    have cw : Covers [⟨c.W + BitVec.ofNat 64 tailO, n⟩] s₁.wr :=
      VG.Proof.AesCcm.RISCV64.covers_prefix (E₁.perm.wC (d := tailO) (n := 16) (by decide)) (by omega)
    have A : WP isa (.block [mov .a0 .s6, .addi .a1 .s1 (tailO : Int), mov .a2 .s7]) s₁ fun s₄ => PK s₁ s₄ ∧
        s₄.mem = s₁.mem ∧ s₄.gpr .s7 = s₁.gpr .s7 ∧ BytesPre s₄ P (c.W + BitVec.ofNat 64 tailO) n := by
      refine wp_mv fun s₂ u₂ => wp_addi (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ =>
        WP.block_nil ⟨(PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)),
          by rw [u₄.mem, u₃.mem, u₂.mem], by rw [u₄.other _ (by decide), u₃.other _ (by decide),
            u₂.other _ (by decide)], ?_⟩
      exact ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h19],
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), E₁.s1],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h20₁], by omega, by omega,
        by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hP.rd,
        by rw [u₄.wr, u₃.wr, u₂.wr]; exact cw,
        (hP.wd (d := tailO) (k := 16) (by decide)).sub_right (Region.sub_prefix (by omega))⟩
    refine WP.seq (WP.mono A fun s₄ ⟨pk₄, m₄, r20₄, hb⟩ => WP.mono (copy_wp s₄ hb) fun s₅ ⟨m₅, _, k₅⟩ =>
      ⟨pk₄.trans (PK.ofKeeps k₅), by rw [k₅.gpr .s7 (by decide), r20₄], ?_⟩)
    rw [m₅, m₄, pmem, m₁]

/-- `0x80` after `P` (`n` bytes) in the tail, `dbl(D)` into `W + 272` and
the XOR of it into the tail. -/
theorem shortPad_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {n : Nat} (hn : n < 16)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa (.block (([.add .t0 .s1 .s7, .li .t1 0x80, .store .b .t1 .t0 tailO] : List Instr) ++
      Impl.Cmac.RISCV64.dbl 16 0x87 dO dbO ++ xor16 tailO dbO tailO)) s fun s' => PK s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩, ⟨c.W + BitVec.ofNat 64 dbO, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) 16 =
        Spec.Cmac.xor (bytesAt (s.mem.writeW (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n) (0x80 : Byte))
            (c.W + BitVec.ofNat 64 tailO) 16)
          (Spec.Cmac.dbl 16 (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16)) := by
  have ww := L.ww
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => ?_
  have a80 : s₂.gpr .t0 + BitVec.ofNat 64 tailO = c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n := by
    rw [u₂.other _ (by decide), u₁.gpr, E.s1, h20, Offset.add_add, Offset.add_add, Nat.add_comm]
  refine wp_sb (by decide) a80 (by
      rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by simp only [tailO]; omega)) fun s₃ u₃ => ?_
  have pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofMupd u₃))
  have E₃ := E.of_pk pk₃
  have b : (BitVec.setWidth 8 (BitVec.ofNat 64 128) : Byte) = 0x80 := by decide
  have m₃ : s₃.mem = s.mem.writeW (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n) (0x80 : Byte) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.mem, b]
  have fP : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem s₃.mem := by
    rw [m₃]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := n) (n := 8 / 8) (k := 16) (by omega) (by omega))
  refine Proof.Cmac.RISCV64.dbl_wp (K := c.W) (src := dO) (dst := dbO) (by decide) (by decide)
    Proof.Cmac.RISCV64.dbl_spec16 E₃.s1 (.inr (by decide)) (by decide) (by decide) (by simp only [dbO]; omega)
    (fun j hj => E₃.perm.wR (by simp only [dO]; omega)) (fun j hj => E₃.perm.wW (by simp only [dbO]; omega))
    fun s₄ g₄ rd₄ wr₄ sp₄ f₄ b₄ => ?_
  have pk₄ : PK s₃ s₄ := ⟨rd₄, wr₄, sp₄, fun r hr => g₄ r (fun e => by subst e; exact absurd hr (by decide))
    (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
    (fun e => by subst e; exact absurd hr (by decide))⟩
  have E₄ := E₃.of_pk pk₄
  rw [← List.append_nil (xor16 tailO dbO tailO)]
  refine xor16_wp L E₄ (a := tailO) (b := dbO) (d := tailO) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun s₅ pk₅ g₅ m₅ => WP.block_nil ⟨pk₃.trans (pk₄.trans pk₅), ?_, ?_⟩
  · rw [m₅]
    exact ((fP.mono (by simp)).trans (f₄.mono (by simp))).trans ((Proof.Cmac.xor2Mem_frame _ _ _ _).mono (by simp))
  · have dTB : (⟨c.W + BitVec.ofNat 64 tailO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 dbO, 16⟩ :=
      L.w_w (.inl (by decide)) (by decide) (by decide)
    have dD : (⟨c.W + BitVec.ofNat 64 dO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 tailO, 16⟩ :=
      L.w_w (.inr (by decide)) (by decide) (by decide)
    rw [m₅, Proof.Cmac.xor2Mem_bytes _ (by
        rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide)), b₄,
      Proof.Cmac.bytesAt_frame f₄ (p := c.W + BitVec.ofNat 64 tailO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dTB) (by decide),
      Proof.Cmac.bytesAt_frame fP (p := c.W + BitVec.ofNat 64 dO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by decide), m₃]

/-- The tail after `shortTail`: `pad(P) ⊕ dbl(D)`. -/
theorem shortTail_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (hn : n < 16) (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa shortTail s fun s' => PK s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩, ⟨c.W + BitVec.ofNat 64 dbO, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) 16 =
        Spec.Cmac.xor (Spec.Siv.pad (bytesAt s.mem P n)) (Spec.Siv.dbl (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16)) := by
  have ww := L.ww
  have hlen : (bytesAt s.mem P n).length = n := Proof.Cmac.bytesAt_length _ _ _
  unfold shortTail
  refine WP.seq (zero16_wp L E (d := tailO) (is := []) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ =>
    WP.block_nil ?_)
  show WP isa _ s₁ _
  have E₁ := E.of_pk pk₁
  have pmem : bytesAt s₁.mem P n = bytesAt s.mem P n := by
    rw [m₁]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega)
  refine WP.seq (WP.mono (shortIte_wp E₁ (hP.of_eq pk₁.rd pk₁.wr) hn (by rw [g₁ _ (by decide), h19])
    (by rw [g₁ _ (by decide), h20]) m₁ pmem) fun s₂ ⟨pk₂, r20₂, m₂⟩ => ?_)
  have E₂ := E₁.of_pk pk₂
  refine WP.mono (shortPad_wp L E₂ (n := n) hn (by rw [r20₂, g₁ _ (by decide), h20]))
    fun s₃ ⟨pk₃, f₃, t₃⟩ => ⟨pk₁.trans (pk₂.trans pk₃), ?_, ?_⟩
  -- The memory.
  · have fC : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem s₂.mem := by
      rw [m₂]
      exact (Proof.Cmac.frame_store2 _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n) (k := 16)
          (by omega) (by decide)))
    exact (fC.mono (by simp)).trans f₃
  -- The tail.
  · have dD : (⟨c.W + BitVec.ofNat 64 dO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 tailO, 16⟩ :=
      L.w_w (.inr (by decide)) (by decide) (by decide)
    have pad := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 tailO))
      (c.W + BitVec.ofNat 64 tailO) (bytesAt s.mem P n) (by rw [hlen]; exact hn) (Proof.Cmac.zero2_bytes _ _)
    have fC : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem s₂.mem := by
      rw [m₂]
      exact (Proof.Cmac.frame_store2 _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n) (k := 16)
          (by omega) (by decide)))
    rw [hlen] at pad
    rw [t₃, Proof.Cmac.bytesAt_frame fC (p := c.W + BitVec.ofNat 64 dO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by decide), m₂]
    simp only [copiedMem]
    rw [pad, Spec.Siv.pad, Spec.Siv.dbl, hlen, show 16 - n - 1 = 15 - n by omega]
    rfl

/-- The CMAC of one block. -/
theorem cmacWith_one (ciph : Spec.Cmac.Cipher) (k1 k2 T : List Byte) (hT : T.length = 16) :
    Spec.Siv.cmacWith ciph k1 k2 T = ciph (Spec.Cmac.xor (Spec.Cmac.zeros 16) (Spec.Cmac.lastBlock 16 k1 k2 T)) := by
  rw [Siv.cmacWith_chained, hT, show Spec.Cmac.chainedLen 16 16 = 0 from rfl, List.take_zero, List.drop_zero]
  rfl

/-- `shortMac`: the CMAC of the tail, one complete block, into `W + out`. -/
theorem shortMac_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (shortMac out) s fun s' => PK s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.ctxMac s.mem c.C c.R (bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) 16) := by
  have hRb := L.rb
  have ho : out + 16 ≤ tailO ∨ tailO + 16 ≤ out := by rcases hout with rfl | rfl <;> decide
  have ho' : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  have ho8 : out % 8 = 0 := by rcases hout with rfl | rfl <;> decide
  unfold shortMac shortArgs
  rw [List.append_assoc]
  refine WP.seq (zero16_wp L E (d := out) (by omega) ho8 fun s₁ pk₁ g₁ m₁ => ?_)
  have E₁ := E.of_pk pk₁
  unfold macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_li (by decide) fun t₆ v₆ => WP.block_nil ?_
  have pk₆ : PK s₁ t₆ := (PK.ofUpd v₁).trans ((PK.ofUpd v₂).trans ((PK.ofUpd v₃).trans ((PK.ofUpd v₄).trans
    ((PK.ofUpd v₅).trans (PK.ofUpd v₆)))))
  have E₆ := E₁.of_pk pk₆
  have F := fargs L E₆ (y := out) ho' (Nat.le_refl 16) (L.srcW E₆.perm (t := tailO) (k := 16) (by decide))
    (L.w_w (by omega) (by decide) (by omega))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₁.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₁.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.gpr])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1]; rfl)
  have m₆ : t₆.mem = s₁.mem := by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine WP.mono (fin_call_raw F) fun s₂ h₂ => ⟨pk₁.trans (pk₆.trans (PK.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved)),
    ?_, ?_⟩
  · have f₁ : Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩] s.mem s₁.mem := by
      rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
    exact f₁.trans (by rw [← m₆]; exact h₂.frame)
  -- What the call reads.
  have dC : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 out, 16⟩ : Region)],
      (⟨c.C + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' hd (by omega)
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame f₁ (dC hd) (by omega)
  have sch := cK (d := 0) (k := 16 * (c.R + 1)) (by omega)
  rw [BitVec.add_zero] at sch
  have tl : bytesAt s₁.mem (c.W + BitVec.ofNat 64 tailO) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) 16 :=
    Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by decide) (by omega)) (by decide)
  have z : bytesAt s₁.mem (c.W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  rw [h₂.out, m₆, Proof.CmacAes.RISCV64.mn, Proof.CmacAes.RISCV64.ciphAt, sch, cK (d := 240) (k := 16) (by decide),
    cK (d := 256) (k := 16) (by decide), tl, z, Spec.Siv.ctxMac, Spec.Siv.schedCiph,
    cmacWith_one _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

/-- S2V's end for a string `P` shorter than a block, into `W + out`. -/
theorem short_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (hn : n < 16) (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) {out : Nat}
    (hout : out = 0 ∨ out = tO) :
    WP isa (.seq shortTail (shortMac out)) s fun s' => PK s s' ∧ Frame (oR c out) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
          (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16) (bytesAt s.mem P n) := by
  have hRb := L.rb
  refine WP.seq (WP.mono (shortTail_wp L E hP hn h19 h20) fun s₁ ⟨pk₁, f₁, t₁⟩ => ?_)
  refine WP.mono (shortMac_wp L (E.of_pk pk₁) hout) fun s₂ ⟨pk₂, f₂, o₂⟩ => ⟨pk₁.trans pk₂, ?_, ?_⟩
  · refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 240, 2336⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · have dc : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 tailO, 16⟩ : Region), ⟨c.W + BitVec.ofNat 64 dbO, 16⟩],
        (⟨c.C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.c0_w' (by decide) (by decide)
      · exact L.c0_w' (by decide) (by decide)
    rw [o₂, t₁, ctxMac_frame f₁ dc hRb, Siv.s2vFinish_short _ _ (by rw [Proof.Cmac.bytesAt_length]; exact hn),
      Siv.xor_eq, Proof.Cmac.xor_comm]

end VG.Proof.AesSiv.RISCV64
