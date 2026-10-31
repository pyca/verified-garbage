module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.S2v
import VerifiedGarbage.Proof.CmacAes.PPC64LE.FinSteps
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.AesSiv.PPC64LE.FinRaw
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Finalize
public import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-SIV on PPC64LE: finishing S2V with a string shorter than a block

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, `shortTail` zeroes the tail at `W + 32`, copies `P` into it
and puts `0x80` after it, so the tail is `pad(P)`, doubles `D` into
`W + 256` and XORs it into the tail (`shortTail_wp`); `shortMac` computes
the CMAC of the tail, one complete block, into `W + out` (`shortMac_wp`),
which is S2V's end (`Siv.s2vFinish_short`, `short_wp`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE VG.WriteBytes
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Impl.Gather.PPC64LE (copyBytes)
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_add wp_stb)
open VG.Proof.CmacAes.Stream.PPC64LE (FArgs)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.Gather.PPC64LE (BytesPre copyBytes_wp Keeps)
open VG.Spec.Aes (bytesAt)

/-- What S2V's end writes: `wR` and its result at `W + out`. -/
abbrev oR (c : Cx) (out : Nat) : List Region := ⟨c.W + BitVec.ofNat 64 out, 16⟩ :: wR c

theorem frame_oR {c : Cx} {m m' : Mem} (out : Nat) (h : Frame (wR c) m m') : Frame (oR c out) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem copyRegs_keep : ∀ r ∈ keepRegs, r ∉ VG.Proof.Gather.PPC64LE.copyRegs := by decide

theorem PK.ofKeeps {s t : State} (h : Keeps s t) : PK s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (copyRegs_keep r hr)⟩

/-- The tail after the copy: `P` on zeros. -/
abbrev copiedMem (m : Mem) (W : Addr) (xs : List Byte) : Mem :=
  writeBytes (Proof.Cmac.zero2 m (W + BitVec.ofNat 64 tailO)) (W + BitVec.ofNat 64 tailO) xs

/-- `P` copied onto the zeroed tail (zeroed from `m₀`), if it is not empty. -/
theorem shortIte_wp {c : Cx} {s₁ : State} (E₁ : Env c s₁) {P : Addr} {n : Nat} (hP : Buf c s₁ P n)
    (hn : n < 16) (h19 : s₁.gpr .r19 = P) (h20₁ : s₁.gpr .r20 = BitVec.ofNat 64 n) {m₀ : Mem}
    (m₁ : s₁.mem = Proof.Cmac.zero2 m₀ (c.W + BitVec.ofNat 64 tailO)) (pmem : bytesAt s₁.mem P n = bytesAt m₀ P n) :
    WP isa (.ite (.zero .d .r20) (.block []) (.seq (.block [mov .r3 .r19, .addi .r9 .r14 tailO, mov .r4 .r20])
        copyBytes)) s₁ fun s' => PK s₁ s' ∧ s'.gpr .r20 = s₁.gpr .r20 ∧
      s'.mem = copiedMem m₀ c.W (bytesAt m₀ P n) := by
  refine WP.ite (decide (n = 0)) (VG.Proof.Gather.PPC64LE.eval_zero h20₁ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨PK.refl _, rfl, ?_⟩
    rw [m₁]; simp [bytesAt, writeBytes_nil]
  · have h0 : n ≠ 0 := by simpa using hf
    have A : WP isa (.block [mov .r3 .r19, .addi .r9 .r14 tailO, mov .r4 .r20]) s₁ fun s₄ => PK s₁ s₄ ∧
        s₄.mem = s₁.mem ∧ s₄.gpr .r20 = s₁.gpr .r20 ∧ BytesPre s₄ P (c.W + BitVec.ofNat 64 tailO) n := by
      refine wp_mv fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ =>
        WP.block_nil ⟨(PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)),
          by rw [u₄.mem, u₃.mem, u₂.mem], by rw [u₄.other _ (by decide), u₃.other _ (by decide),
            u₂.other _ (by decide)], ?_⟩
      exact ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h19],
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), E₁.r14],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h20₁], by omega_arith, by omega_arith,
        by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hP.rd,
        by rw [u₄.wr, u₃.wr, u₂.wr]; exact Proof.Gather.PPC64LE.covers_prefix (E₁.perm.wC (d := tailO) (n := 16)
          (by decide)) (by omega_arith),
        (hP.wd (d := tailO) (k := 16) (by decide)).sub_right (Region.sub_prefix (by omega_arith))⟩
    refine WP.seq (WP.mono A fun s₄ ⟨pk₄, m₄, r20₄, hb⟩ => WP.mono (copyBytes_wp s₄ hb) fun s₅ ⟨m₅, _, k₅⟩ =>
      ⟨pk₄.trans (PK.ofKeeps k₅), by rw [k₅.gpr .r20 (by decide), r20₄], ?_⟩)
    rw [m₅, m₄, pmem, m₁]

/-- The memory after `0x80` after `P` in the tail. -/
abbrev paddedMem (m : Mem) (W : Addr) (xs : List Byte) : Mem :=
  (copiedMem m W xs).writeW (W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 xs.length) (0x80 : Byte)

/-- The memory after `shortTail`. -/
abbrev shortMem (m : Mem) (W : Addr) (xs : List Byte) : Mem :=
  Proof.Cmac.xor2Mem (Proof.CmacAes.PPC64LE.dblMem (paddedMem m W xs) W dO dbO) (W + BitVec.ofNat 64 tailO)
    (W + BitVec.ofNat 64 tailO) (W + BitVec.ofNat 64 dbO)

/-- `0x80` after `P`, `dbl(D)` and the XOR, but for the stack pointer. -/
theorem shortPad_wp' {c : Cx} {s : State} (E : Env c s) {xs : List Byte} (hn : xs.length < 16)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 xs.length) :
    WP isa (.block (([.add .r9 .r14 .r20, .li .r0 0x80, .stb .r0 .r9 tailO] : List Instr) ++
      Impl.CmacAes.PPC64LE.dbl dO dbO ++ xor16 tailO dbO tailO)) s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ keepRegs, s'.gpr r = s.gpr r) ∧ s'.mem = Proof.Cmac.xor2Mem
        (Proof.CmacAes.PPC64LE.dblMem (s.mem.writeW (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 xs.length)
          (0x80 : Byte)) c.W dO dbO) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 tailO)
          (c.W + BitVec.ofNat 64 dbO) := by
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => ?_
  have a80 : s₂.gpr .r9 + BitVec.ofNat 64 tailO = c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 xs.length := by
    rw [u₂.other _ (by decide), u₁.gpr, E.r14, h20, Offset.add_add, Offset.add_add, Nat.add_comm]
  refine wp_stb (by decide) (by decide) a80 (by
      rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by simp only [tailO]; omega_arith)) fun s₃ u₃ => ?_
  have r14₃ : s₃.gpr .r14 = c.W := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r14]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have P₃ := E.perm.of_eq rd₃ wr₃
  refine Proof.CmacAes.PPC64LE.dbl_wp r14₃ (by decide) (by decide) (P₃.wR (by decide))
    (P₃.wR (by decide)) (P₃.wW (by decide)) (P₃.wW (by decide)) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have r14₄ : s₄.gpr .r14 = c.W := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), r14₃]
  have P₄ := P₃.of_eq rd₄ wr₄
  show WP isa (.block (Proof.CmacAes.PPC64LE.xor2 .r14 .r14 .r14 tailO dbO tailO ++ [])) s₄ _
  refine Proof.CmacAes.PPC64LE.xor2_wp .r14 .r14 .r14 tailO dbO tailO (P := c.W + BitVec.ofNat 64 tailO)
    (Q := c.W + BitVec.ofNat 64 dbO) (C := c.W + BitVec.ofNat 64 tailO) ⟨by decide, by decide, by decide⟩
    (by decide) (by decide) (by decide) (by rw [r14₄]) (by rw [r14₄, Offset.add_add]) (by rw [r14₄])
    (by rw [r14₄, Offset.add_add]) (by rw [r14₄]) (by rw [r14₄, Offset.add_add]) (by decide)
    (P₄.wR (by decide)) (by rw [Offset.add_add]; exact P₄.wR (by decide)) (P₄.wR (by decide))
    (by rw [Offset.add_add]; exact P₄.wR (by decide)) (P₄.wW (by decide))
    (by rw [Offset.add_add]; exact P₄.wW (by decide)) fun s₅ g₅ m₅ rd₅ wr₅ =>
      WP.block_nil ⟨by rw [rd₅, rd₄, rd₃], by rw [wr₅, wr₄, wr₃], fun r hr => ?_, ?_⟩
  · have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    have h9 : r ≠ .r9 := fun e => by subst e; exact absurd hr (by decide)
    have h10 : r ≠ .r10 := fun e => by subst e; exact absurd hr (by decide)
    have h11 : r ≠ .r11 := fun e => by subst e; exact absurd hr (by decide)
    have h12 : r ≠ .r12 := fun e => by subst e; exact absurd hr (by decide)
    rw [g₅ _ h9 h10, g₄ _ h9 h10 h11 h12, u₃.gpr, u₂.other _ h0, u₁.other _ h9]
  · have b : (BitVec.setWidth 8 (BitVec.ofNat 64 128) : Byte) = 0x80 := by decide
    rw [m₅, m₄, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, b]

/-- `0x80` after `P`, `dbl(D)` and the XOR. -/
theorem shortPad_wp {c : Cx} {s : State} (E : Env c s) {xs : List Byte} (hn : xs.length < 16)
    (h20 : s.gpr .r20 = BitVec.ofNat 64 xs.length) :
    WP isa (.block (([.add .r9 .r14 .r20, .li .r0 0x80, .stb .r0 .r9 tailO] : List Instr) ++
      Impl.CmacAes.PPC64LE.dbl dO dbO ++ xor16 tailO dbO tailO)) s fun s' => PK s s' ∧ s'.mem = Proof.Cmac.xor2Mem
        (Proof.CmacAes.PPC64LE.dblMem (s.mem.writeW (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 xs.length)
          (0x80 : Byte)) c.W dO dbO) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 tailO)
          (c.W + BitVec.ofNat 64 dbO) :=
  WP.mono (VG.Proof.AesCbc.PPC64LE.wp_sp (shortPad_wp' E hn h20)) fun _ ⟨⟨rd, wr, g, m⟩, sp⟩ => ⟨⟨rd, wr, sp, g⟩, m⟩

/-- The tail after `shortTail`: `pad(P) ⊕ dbl(D)`. -/
theorem shortTail_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (hn : n < 16) (h19 : s.gpr .r19 = P) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) :
    WP isa shortTail s fun s' => PK s s' ∧
      Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩, ⟨c.W + BitVec.ofNat 64 dbO, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 tailO) 16 =
        Spec.Cmac.xor (Spec.Siv.pad (bytesAt s.mem P n)) (Spec.Siv.dbl (bytesAt s.mem (c.W + BitVec.ofNat 64 dO) 16)) := by
  have ww := L.ww
  have hlen : (bytesAt s.mem P n).length = n := Proof.Cmac.bytesAt_length _ _ _
  unfold shortTail
  refine WP.seq (zero16_wp E (d := tailO) (is := []) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ =>
    WP.block_nil ?_)
  show WP isa _ s₁ _
  have E₁ := E.of_pk pk₁
  have pmem : bytesAt s₁.mem P n = bytesAt s.mem P n := by
    rw [m₁]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega_arith)
  refine WP.seq (WP.mono (shortIte_wp E₁ (hP.of_eq pk₁.rd pk₁.wr) hn (by rw [g₁ _ (by decide), h19])
    (by rw [g₁ _ (by decide), h20]) m₁ pmem) fun s₂ ⟨pk₂, r20₂, m₂⟩ => ?_)
  have E₂ := E₁.of_pk pk₂
  refine WP.mono (shortPad_wp E₂ (xs := bytesAt s.mem P n) (by omega_arith)
    (by rw [r20₂, g₁ _ (by decide), h20, hlen])) fun s₃ ⟨pk₃, m₃⟩ => ⟨pk₁.trans (pk₂.trans pk₃), ?_, ?_⟩
  -- The memory.
  · have dT : (⟨c.W + BitVec.ofNat 64 tailO, 16⟩ : Region).Contains
        (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n) (8 / 8) := by
      exact Offset.contains_base _ (d := n) (n := 8 / 8) (k := 16) (by omega_arith) (by omega_arith)
    have fP : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem
        ((copiedMem s.mem c.W (bytesAt s.mem P n)).writeW (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 n)
          (0x80 : Byte)) :=
      ((Proof.Cmac.frame_store2 _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n) (k := 16)
          (by omega_arith) (by decide)))).writeW (List.mem_singleton_self _) _ dT
    rw [m₃, m₂, hlen]
    exact ((fP.mono (by simp)).trans ((Proof.CmacAes.PPC64LE.dblMem_frame _ _ _ _).mono (by simp))).trans
      ((Proof.Cmac.xor2Mem_frame _ _ _ _).mono (by simp))
  -- The tail.
  · have dTB : (⟨c.W + BitVec.ofNat 64 tailO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 dbO, 16⟩ :=
      L.w_w (.inl (by decide)) (by decide) (by decide)
    have dD : (⟨c.W + BitVec.ofNat 64 dO, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 tailO, 16⟩ :=
      L.w_w (.inr (by decide)) (by decide) (by decide)
    have pad := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 tailO))
      (c.W + BitVec.ofNat 64 tailO) (bytesAt s.mem P n) (by rw [hlen]; exact hn) (Proof.Cmac.zero2_bytes _ _)
    have fP : Frame [⟨c.W + BitVec.ofNat 64 tailO, 16⟩] s.mem
        ((copiedMem s.mem c.W (bytesAt s.mem P n)).writeW
          (c.W + BitVec.ofNat 64 tailO + BitVec.ofNat 64 (bytesAt s.mem P n).length) (0x80 : Byte)) := by
      rw [hlen]
      exact ((Proof.Cmac.frame_store2 _ _ _).trans (writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base (c.W + BitVec.ofNat 64 tailO) (d := 0) (n := n) (k := 16)
          (by omega_arith) (by decide)))).writeW (List.mem_singleton_self _) _ (by
        exact Offset.contains_base _ (d := n) (n := 8 / 8) (k := 16) (by omega_arith) (by omega_arith))
    rw [m₃, m₂, Proof.Cmac.xor2Mem_bytes _ (by
        rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by rw [Offset.add_add]; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      Proof.CmacAes.PPC64LE.dblMem_bytes,
      Proof.Cmac.bytesAt_frame (Proof.CmacAes.PPC64LE.dblMem_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dTB) (by decide),
      Proof.Cmac.bytesAt_frame fP (p := c.W + BitVec.ofNat 64 dO) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by decide),
      pad, Spec.Siv.pad, Spec.Siv.dbl, hlen, show 16 - n - 1 = 15 - n by omega_arith]
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
  have ho8 : out % 4 = 0 := by rcases hout with rfl | rfl <;> decide
  unfold shortMac shortArgs
  rw [List.append_assoc]
  refine WP.seq (zero16_wp E (d := out) (by omega_arith) ho8 fun s₁ pk₁ g₁ m₁ => ?_)
  have E₁ := E.of_pk pk₁
  unfold macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) (by decide) fun t₄ v₄ => wp_addi (by decide) (by decide) fun t₅ v₅ =>
    wp_li (by decide) fun t₆ v₆ => WP.block_nil ?_
  have pk₆ : PK s₁ t₆ := (PK.ofUpd v₁).trans ((PK.ofUpd v₂).trans ((PK.ofUpd v₃).trans ((PK.ofUpd v₄).trans
    ((PK.ofUpd v₅).trans (PK.ofUpd v₆)))))
  have E₆ := E₁.of_pk pk₆
  have F := fargs L E₆ (y := out) ho' (Nat.le_refl 16) (L.srcW E₆.perm (t := tailO) (k := 16) (by decide))
    (L.w_w (by omega_arith) (by decide) (by omega_arith))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₁.r15])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₁.r16])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.r14])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.r14])
    (by rw [v₆.gpr])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.r14]; rfl)
  have m₆ : t₆.mem = s₁.mem := by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  refine WP.mono (fin_call_raw F) fun s₂ h₂ => ⟨pk₁.trans (pk₆.trans (PK.ofSaved h₂.rd h₂.wr h₂.sp h₂.saved)),
    ?_, ?_⟩
  · have f₁ : Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩] s.mem s₁.mem := by
      rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
    exact f₁.trans (by rw [← m₆]; exact h₂.frame)
  -- What the call reads.
  have dC : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 out, 16⟩ : Region)],
      (⟨c.C + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' hd (by omega_arith)
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 out, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame f₁ (dC hd) (by omega_arith)
  have sch := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_arith)
  rw [BitVec.add_zero] at sch
  have tl : bytesAt s₁.mem (c.W + BitVec.ofNat 64 tailO) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 tailO) 16 :=
    Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) (by decide) (by omega_arith)) (by decide)
  have z : bytesAt s₁.mem (c.W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  rw [h₂.out, m₆, Proof.CmacAes.PPC64LE.mn, Proof.CmacAes.PPC64LE.ciphAt, sch, cK (d := 240) (k := 16) (by decide),
    cK (d := 256) (k := 16) (by decide), tl, z, Spec.Siv.ctxMac, Spec.Siv.schedCiph,
    cmacWith_one _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

/-- S2V's end for a string `P` shorter than a block, into `W + out`. -/
theorem short_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (hn : n < 16) (h19 : s.gpr .r19 = P) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) {out : Nat}
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

end VG.Proof.AesSiv.PPC64LE
