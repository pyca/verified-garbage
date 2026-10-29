module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.CmacTripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls

/-!
# Streaming TDEA-CMAC on RISC-V: `finish`

The code saves `ra`, `s1`–`s3` (`finSave_wp`), computes the number `h` of
bytes held back, and points `t5` at the last block and `t6` at its subkey:
the block held back and `K1` if it is complete (`complete_wp`), else the
bytes held back copied onto a zeroed block in the scratch buffer and padded
there (`padded_wp`, `Proof.CmacTripleDes.padded_bytes8`) and `K2`. Their XOR
is §6.2's last block (`FBr`), which the code XORs into the chaining value in
the state (`xor_xor`), enciphers in place, and copies to `out`, which is the
MAC (`finish_spec`, as on PPC64LE).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.Proof.CmacTripleDes.Stream (held)
open VG.WriteBytes (writeBytes)

/-- The precondition, by name: the state `St`, `out` at `O`, the scratch
buffer `S`, and `count = n`. -/
structure FPre (s₀ : State) (St O S : Addr) (n : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a1 : s₀.gpr .a1 = BitVec.ofNat 64 n
  a2 : s₀.gpr .a2 = O
  a3 : s₀.gpr .a3 = S
  hn : n < 2 ^ 64
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 416⟩, ⟨O, 8⟩, ⟨S, 640⟩]
  st_o : (⟨St, 416⟩ : Region).Disjoint ⟨O, 8⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩
  o_s : (⟨O, 8⟩ : Region).Disjoint ⟨S, 640⟩
  stk_st : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨St, 416⟩
  stk_o : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨O, 8⟩
  stk_s : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨S, 640⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wO : O.toNat + 8 ≤ 2 ^ 64
  wS : S.toNat + 640 ≤ 2 ^ 64
  al : s₀.sp.toNat % 16 = 0
  sp : 944 ≤ s₀.sp.toNat

theorem FPre.of {s₀ : State} (h : finishRISCV64.pre s₀) :
    FPre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, ofNat_toNat_eq rfl, rfl, rfl, (s₀.gpr .a1).isLt, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- What the code saves: the registers, with `t0` the slots' base. -/
abbrev finG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv S)).gpr

theorem fin_bound : ∀ p ∈ finSaved, p.2 + 8 ≤ 32 := by decide

/-! ## Bytes -/

/-- XOR is associative and commutative on blocks. -/
theorem xor_xor : ∀ (a b c : List Byte), b.length = a.length → c.length = a.length →
    Spec.Cmac.xor (Spec.Cmac.xor a b) c = Spec.Cmac.xor a (Spec.Cmac.xor c b)
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | x :: a, y :: b, z :: c, hb, hc => by
    simp only [Spec.Cmac.xor, List.zipWith_cons_cons, List.cons.injEq] at *
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hb hc
    exact ⟨by rw [BitVec.xor_assoc, BitVec.xor_comm y z], xor_xor a b c hb hc⟩

/-- The bytes `xorBytes` leaves at its destination. -/
theorem xorBytes_bytes {t u dst src : Reg} {s s' : State} (h : Bytes.XorI t u dst src 8 s 8 s') :
    Spec.Aes.bytesAt s'.mem (s.gpr dst) 8 =
      Spec.Cmac.xor (Spec.Aes.bytesAt s.mem (s.gpr dst) 8) (Spec.Aes.bytesAt s.mem (s.gpr src) 8) := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt, Spec.Cmac.xor])
  intro j h₁ _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
  simp only [Spec.Aes.bytesAt, Spec.Cmac.xor, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact h.xored j h₁

/-- The block `finish` enciphers, for a state that represents `msg`: its
cipher is the MAC. -/
theorem finish_spec {m : Mem} {St : Addr} {key msg : List Byte} (hr : Spec.Cmac.tdesRepr m St key msg) :
    Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m St)
      (Spec.Cmac.xor (Spec.Aes.bytesAt m (St + BitVec.ofNat 64 400) 8)
        (Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (St + BitVec.ofNat 64 384) 8)
          (Spec.Aes.bytesAt m (St + BitVec.ofNat 64 392) 8)
          (Spec.Aes.bytesAt m (St + BitVec.ofNat 64 408) (held msg.length)))) =
      Spec.Cmac.tdesCmac key 8 msg := by
  obtain ⟨hm, hne, hc, hcat⟩ := Proof.CmacTripleDes.Stream.repr_finish hr
  obtain ⟨-, hs, hk, -, -⟩ := hr
  have hks : Spec.Aes.bytesAt m (St + BitVec.ofNat 64 384) 8 = (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).1 ∧
      Spec.Aes.bytesAt m (St + BitVec.ofNat 64 392) 8 = (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).2 := by
    have hl1 : (Spec.Cmac.subkeys (Spec.Cmac.tdes key) 8).1.length = 8 := by
      rw [Spec.Cmac.tdes, Proof.CmacTripleDes.subkeys_tdes]; exact Proof.Cmac.length_le8 _
    have e := hk
    rw [show (St + 384 : Addr) = St + BitVec.ofNat 64 384 from rfl, Proof.Cmac.bytesAt_split, Offset.add_add,
      show (384 + 8 : Nat) = 392 from rfl] at e
    exact List.append_inj e (by simp [Spec.Aes.bytesAt, hl1])
  have hl := Proof.CmacTripleDes.Stream.held_le msg.length
  rw [Proof.CmacTripleDes.Stream.tdesCmac_eq]
  conv => rhs; rw [← hcat]
  rw [Proof.CmacTripleDes.macFull_split8 _ hm (by simp [Spec.Aes.bytesAt]; omega) (by
      rcases hne with h | h
      · exact .inl h
      · exact .inr (by simp [Spec.Aes.bytesAt]; omega))]
  rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl, show St + 408 = St + BitVec.ofNat 64 408 from rfl] at *
  rw [← hc, ← hks.1, ← hks.2, hs]
  rfl


/-! ## Before the branch -/

/-- What `finSave` leaves. -/
structure FMid₁ (s₀ : State) (St O S : Addr) (n : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = O
  a1 : s.gpr .a1 = BitVec.ofNat 64 n
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s.gpr r = s₀.gpr r
  mem : s.mem = Spill.saveMem s₀.mem (sv S) (finG s₀ S) finSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem finSave_wp {s₀ : State} {St O S : Addr} {n : Nat} (hp : FPre s₀ St O S n) :
    WP isa (.block finSave) s₀ (FMid₁ s₀ St O S n) := by
  rw [finSave, saveRegs, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a3) fun s₁ e => ?_
  subst e
  rw [hp.a3, show finSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 finSaved from rfl]
  have t₀ : (s₀.write .t0 (sv S)).gpr .t0 = sv S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := finSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := fin_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 640⟩, by simp, sv_contains S (by omega) (by decide)⟩
  generalize ht : ({ (s₀.write .t0 (sv S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv S)).mem ((s₀.write .t0 (sv S)).gpr .t0)
      (s₀.write .t0 (sv S)).gpr finSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have memt : t.mem = Spill.saveMem s₀.mem (sv S) (finG s₀ S) finSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, fun r hr h1 h2 h3 => ?_, ?_, by rw [u₃.rd, u₂.rd, u₁.rd, rdt],
    by rw [u₃.wr, u₂.wr, u₁.wr, wrt], by rw [u₃.sp, u₂.sp, u₁.sp, spt]⟩
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.gpr, gt, hp.a0]
  · simp (disch := decide) only [u₃.other, u₂.gpr, u₁.other, gt, hp.a3]
  · simp (disch := decide) only [u₃.gpr, u₂.other, u₁.other, gt, hp.a2]
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.other, gt, hp.a1]
  · obtain ⟨h0, -⟩ := preserved_ne r hr
    rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1, gt _ h0]
  · rw [u₃.mem, u₂.mem, u₁.mem, memt]

/-! ## The last block -/

/-- The last block's address: the block held back if it is complete, else
the padded block. -/
def mpOf (St S : Addr) (h : Nat) : Addr := if h = 8 then St + BitVec.ofNat 64 408 else S + BitVec.ofNat 64 64

/-- The last block's subkey's address: `K1`'s if it is complete, else `K2`'s. -/
def kpOf (St : Addr) (h : Nat) : Addr := if h = 8 then St + BitVec.ofNat 64 384 else St + BitVec.ofNat 64 392

/-- What the branch leaves, from the memory `m` before it: the last block at
`t5` and its subkey at `t6`, whose XOR is §6.2's last block of the bytes
held back, and the memory changed only in the padded block. -/
structure FBr (St S : Addr) (h : Nat) (u : State) (m : Mem) (s : State) : Prop where
  keep : ∀ r ∈ preserved, s.gpr r = u.gpr r
  rd : s.rd = u.rd
  wr : s.wr = u.wr
  sp : s.sp = u.sp
  frame : Frame [⟨S + BitVec.ofNat 64 64, 8⟩] m s.mem
  t5 : s.gpr .t5 = mpOf St S h
  t6 : s.gpr .t6 = kpOf St h
  blk : ∃ Mp Kp, s.gpr .t5 = Mp ∧ s.gpr .t6 = Kp ∧ (Mp = St + BitVec.ofNat 64 408 ∨ Mp = S + BitVec.ofNat 64 64) ∧
    (Kp = St + BitVec.ofNat 64 384 ∨ Kp = St + BitVec.ofNat 64 392) ∧
    Spec.Cmac.xor (Spec.Aes.bytesAt s.mem Kp 8) (Spec.Aes.bytesAt s.mem Mp 8) =
      Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (St + BitVec.ofNat 64 384) 8)
        (Spec.Aes.bytesAt m (St + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m (St + BitVec.ofNat 64 408) h)

theorem complete_wp {u : State} {St S : Addr} (h1 : u.gpr .s1 = St) :
    WP isa (.block complete) u (FBr St S 8 u u.mem) := by
  unfold complete
  refine wp_addi (imm := 408) (by decide) fun s₁ u₁ => wp_addi (imm := 384) (by decide) fun s₂ u₂ =>
    WP.block_nil ?_
  have m₂ : s₂.mem = u.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨fun r hr => ?_, by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp],
    by rw [m₂]; exact Frame.refl _ _, ?_, ?_, St + BitVec.ofNat 64 408, St + BitVec.ofNat 64 384, ?_, ?_, .inl rfl,
    .inl rfl, ?_⟩
  · obtain ⟨-, -, -, -, -, h5, h6, -⟩ := preserved_ne r hr
    rw [u₂.other _ h6, u₁.other _ h5]
  · rw [u₂.other _ (by decide), u₁.gpr, h1]; rfl
  · rw [u₂.gpr, u₁.other _ (by decide), h1]; rfl
  · rw [u₂.other _ (by decide), u₁.gpr, h1]
  · rw [u₂.gpr, u₁.other _ (by decide), h1]
  · rw [m₂]
    simp only [Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ↓reduceIte]

theorem padded_wp {u : State} {St S : Addr} {h : Nat} (hh : h < 8) (h1 : u.gpr .s1 = St) (h2 : u.gpr .s2 = S)
    (h0 : u.gpr .t0 = BitVec.ofNat 64 h) (hSt : (⟨St, 416⟩ : Region) ∈ u.wr) (hS : (⟨S, 640⟩ : Region) ∈ u.wr)
    (hd : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩) :
    WP isa padded u (FBr St S h u u.mem) := by
  have pSub : Region.Sub ⟨S + BitVec.ofNat 64 64, 8⟩ ⟨S, 640⟩ := Offset.sub_base S (by decide)
  have hSub : Region.Sub ⟨St + BitVec.ofNat 64 408, h⟩ ⟨St, 416⟩ := Offset.sub_base St (by omega)
  have dPad : ∀ d k, d + k ≤ 416 → ∀ r ∈ [(⟨S + BitVec.ofNat 64 64, 8⟩ : Region)],
      (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun d k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left (Offset.sub_base St hk)).sub_right pSub
  unfold padded padStart
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t2) (dst := .s2) (doff := 64) (bs := List.replicate 8 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₁ hs₁ => ?_
  · simp only [List.length_replicate] at hi
    rw [h2]; exact ⟨_, hS, Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨z₁, fz₁⟩ := zeros_stored (C := S + BitVec.ofNat 64 64) (by rw [h2]) hs₁
  unfold mov
  refine wp_addi (imm := 64) (by decide) fun s₂ u₂ => wp_addi (imm := 408) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s₄.gpr r = u.gpr r := fun r a b c d => by
    rw [u₄.other _ d, u₃.other _ c, u₂.other _ b, hs₁.gpr _ a]
  have wr₄ : s₄.wr = u.wr := by rw [u₄.wr, u₃.wr, u₂.wr, hs₁.wr]
  have rd₄ : s₄.rd = u.rd := by rw [u₄.rd, u₃.rd, u₂.rd, hs₁.rd]
  have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have hcp := copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s₄ (P := St + BitVec.ofNat 64 408) (C := S + BitVec.ofNat 64 64) (L := h)
    (by omega) (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), hs₁.gpr _ (by decide), h1])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hs₁.gpr _ (by decide), h2])
    (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), hs₁.gpr _ (by decide), h0])
    (fun i hi => by rw [rd₄, wr₄, Offset.add_add]; exact in_wr (s := u) ⟨_, hSt, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [wr₄, Offset.add_add]; exact ⟨_, hS, Offset.contains_base _ (by omega) (by omega)⟩)
    ((hd.sub_left hSub).sub_right (fun a ha => pSub a (Region.sub_prefix (by omega) a ha)))
  refine WP.seq (WP.mono (wp_sp hcp) fun s₅ ⟨c₅, sp₅⟩ => ?_)
  have g₅ : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → s₅.gpr r = u.gpr r := fun r a b c d e => by
    rw [c₅.other r e c b d, g₄ r a b c d]
  unfold padDone
  refine wp_addi (imm := 64) (by decide) fun s₆ u₆ => wp_add fun s₇ u₇ => wp_li (imm := 0x80) (by decide)
    fun s₈ u₈ => ?_
  have t3₈ : s₈.gpr .t3 = S + BitVec.ofNat 64 64 + BitVec.ofNat 64 h := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide)
      (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h2, h0]
  have wr₈ : s₈.wr = u.wr := by rw [u₈.wr, u₇.wr, u₆.wr, c₅.wr, wr₄]
  refine wp_sb (a := S + BitVec.ofNat 64 64 + BitVec.ofNat 64 h) (by decide) (by rw [t3₈, BitVec.add_zero])
    (by rw [wr₈, Offset.add_add]; exact ⟨_, hS, Offset.contains_base _ (by omega) (by omega)⟩) fun s₉ g₉ => ?_
  refine wp_addi (imm := 64) (by decide) fun s₁₀ u₁₀ => wp_addi (imm := 392) (by decide) fun s₁₁ u₁₁ =>
    WP.block_nil ?_
  have m₁₁ : s₁₁.mem = (writeBytes s₁.mem (S + BitVec.ofNat 64 64) (Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 408) h)).writeW
      (S + BitVec.ofNat 64 64 + BitVec.ofNat 64 h) (0x80 : Byte) := by
    rw [u₁₁.mem, u₁₀.mem, g₉.mem, u₈.gpr, u₈.mem, u₇.mem, u₆.mem, c₅.mem, m₄]
    rfl
  have xs : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 408) h = Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 408) h :=
    Proof.Cmac.bytesAt_frame fz₁ (dPad 408 h (by omega)) (by omega)
  have hlen : (Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 408) h).length = h := Proof.Cmac.bytesAt_length _ _ _
  have fr : Frame [⟨S + BitVec.ofNat 64 64, 8⟩] u.mem s₁₁.mem := by
    rw [m₁₁]
    refine Frame.trans fz₁ ?_
    have fw := WriteBytes.writeBytes_frame s₁.mem (S + BitVec.ofNat 64 64)
      (Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 408) h) (R := ⟨S + BitVec.ofNat 64 64, 8⟩)
      (by rw [hlen]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    exact fw.writeW
      (List.mem_singleton_self _) _ (by rw [Offset.add_add]; exact Offset.contains _ (by omega) (by omega) (by omega))
  refine ⟨fun r hr => ?_, by rw [u₁₁.rd, u₁₀.rd, g₉.rd, u₈.rd, u₇.rd, u₆.rd, c₅.rd, rd₄],
    by rw [u₁₁.wr, u₁₀.wr, g₉.wr, wr₈], by rw [u₁₁.sp, u₁₀.sp, g₉.sp, u₈.sp, u₇.sp, u₆.sp, sp₅, u₄.sp, u₃.sp,
      u₂.sp, hs₁.sp], fr, ?_, ?_, S + BitVec.ofNat 64 64, St + BitVec.ofNat 64 392, ?_, ?_, .inr rfl, .inr rfl, ?_⟩
  · obtain ⟨-, -, h2', h3', h4', h5', h6', -⟩ := preserved_ne r hr
    rw [u₁₁.other _ h6', u₁₀.other _ h5', g₉.gpr, u₈.other _ h2', u₇.other _ h3', u₆.other _ h3',
      g₅ r h2' h3' h4' h5' h6']
  · simp only [mpOf, show h ≠ 8 by omega, ↓reduceIte]
    rw [u₁₁.other _ (by decide), u₁₀.gpr, g₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h2]
  · simp only [kpOf, show h ≠ 8 by omega, ↓reduceIte]
    rw [u₁₁.gpr, u₁₀.other _ (by decide), g₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h1]
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, g₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h2]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), g₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h1]
  · have k2 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 392) 8 = Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 392) 8 :=
      Proof.Cmac.bytesAt_frame fr (dPad 392 8 (by omega)) (by omega)
    have pb := Proof.CmacTripleDes.padded_bytes8 s₁.mem (S + BitVec.ofNat 64 64)
      (Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 408) h) (by rw [hlen]; exact hh) z₁
    rw [hlen] at pb
    rw [k2, m₁₁, pb, xs, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length]
    simp only [show h ≠ 8 by omega, ↓reduceIte]


/-! ## The whole function -/

/-- A block apart from another holds none of its bytes. -/
theorem nsep {A B : Addr} (h : Region.Disjoint ⟨A, 8⟩ ⟨B, 8⟩) :
    ∀ i < 8, ¬ (⟨A, 8⟩ : Region).Contains (B + BitVec.ofNat 64 i) 1 :=
  fun i hi hc => h _ hc (Offset.contains_base B (by omega) (by omega))

theorem sub8_beq : ∀ h ≤ 8, (BitVec.ofNat 64 h - BitVec.ofNat 64 8 == 0) = decide (h = 8) := by decide


/-- The branch: the last block complete or padded. -/
theorem branch_wp {u : State} {St S : Addr} {h : Nat} (hhl : h ≤ 8) (h1 : u.gpr .s1 = St) (h2 : u.gpr .s2 = S)
    (h0 : u.gpr .t0 = BitVec.ofNat 64 h) (ht1 : u.gpr .t1 = BitVec.ofNat 64 h - BitVec.ofNat 64 8)
    (hSt : (⟨St, 416⟩ : Region) ∈ u.wr) (hS : (⟨S, 640⟩ : Region) ∈ u.wr)
    (hd : (⟨St, 416⟩ : Region).Disjoint ⟨S, 640⟩) :
    WP isa (.ite (.zero .t1) (.block complete) padded) u (FBr St S h u u.mem) := by
  by_cases h8 : h = 8
  · refine WP.ite true (by rw [eval_zero, ht1, sub8_beq _ hhl, h8]; rfl) (fun _ => ?_) (fun h => by cases h)
    rw [h8]; exact complete_wp h1
  · refine WP.ite false (by rw [eval_zero, ht1, sub8_beq _ hhl]; simp [h8]) (fun h => by cases h) fun _ => ?_
    exact padded_wp (by omega) h1 h2 h0 hSt hS hd

/-- What `finXor` leaves: the last block and its subkey XORed into the
chaining value, and ECB's arguments on it. -/
structure FX (St S : Addr) (h : Nat) (s₄ s : State) : Prop where
  args : EArgs s St 400
  keep : ∀ r ∈ preserved, s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  sp : s.sp = s₄.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s₄.mem s.mem
  out : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.xor (Spec.Cmac.xor (Spec.Aes.bytesAt s₄.mem (St + BitVec.ofNat 64 400) 8)
      (Spec.Aes.bytesAt s₄.mem (mpOf St S h) 8)) (Spec.Aes.bytesAt s₄.mem (kpOf St h) 8)

theorem finXor_wp {s₀ s₄ : State} {St O S : Addr} {n h : Nat} (hp : FPre s₀ St O S n)
    (s1₄ : s₄.gpr .s1 = St) (wr₄ : s₄.wr = s₀.wr) (rd₄ : s₄.rd = s₀.rd) (sp₄ : s₄.sp = s₀.sp)
    (t5₄ : s₄.gpr .t5 = mpOf St S h) (t6₄ : s₄.gpr .t6 = kpOf St h) :
    WP isa (.block finXor) s₄ (FX St S h s₄) := by
  have hw := hp.wSt
  have hsw := hp.wS
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have sW : (⟨S, 640⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hM : mpOf St S h = St + BitVec.ofNat 64 408 ∨ mpOf St S h = S + BitVec.ofNat 64 64 := by
    unfold mpOf; split <;> simp
  have hK : kpOf St h = St + BitVec.ofNat 64 384 ∨ kpOf St h = St + BitVec.ofNat 64 392 := by
    unfold kpOf; split <;> simp
  generalize hMe : mpOf St S h = Mp at hM t5₄
  generalize hKe : kpOf St h = Kp at hK t6₄
  have cv : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  have dM : Region.Disjoint ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨Mp, 8⟩ := by
    rcases hM with rfl | rfl
    · exact Offset.disjoint St (.inl (by omega)) (by omega) (by omega)
    · exact (hp.st_s.sub_left cv).sub_right (Offset.sub_base S (by decide))
  have dK : Region.Disjoint ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨Kp, 8⟩ := by
    rcases hK with rfl | rfl
    · exact Offset.disjoint St (.inr (by omega)) (by omega) (by omega)
    · exact Offset.disjoint St (.inr (by omega)) (by omega) (by omega)
  have mIn : ∀ i < 8, InRegions s₀.wr (Mp + BitVec.ofNat 64 i) 1 := by
    intro i hi; rcases hM with rfl | rfl <;> rw [Offset.add_add]
    · exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩
    · exact ⟨_, sW, Offset.contains_base _ (by omega) (by omega)⟩
  have kIn : ∀ i < 8, InRegions s₀.wr (Kp + BitVec.ofNat 64 i) 1 := by
    intro i hi; rcases hK with rfl | rfl <;> rw [Offset.add_add] <;>
      exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩
  have cIn : ∀ i < 8, InRegions s₀.wr (St + BitVec.ofNat 64 400 + BitVec.ofNat 64 i) 1 := by
    intro i hi; rw [Offset.add_add]; exact ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩
  unfold finXor
  rw [List.append_assoc, List.append_assoc, List.singleton_append]
  refine wp_addi (imm := 400) (by decide) fun s₅ u₅ => ?_
  have a0₅ : s₅.gpr .a0 = St + BitVec.ofNat 64 400 := by rw [u₅.gpr, s1₄]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.xorBytes_ok (t := .t2) (u := .t3) (dst := .a0) (src := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [u₅.other _ (by decide), t5₄, u₅.rd, u₅.wr, rd₄, wr₄]; exact in_wr (mIn i hi))
    (fun i hi => by rw [a0₅, u₅.wr, wr₄]; exact cIn i hi)
    (by rw [a0₅, u₅.other _ (by decide), t5₄]; exact nsep dM)) fun s₆ x₆ => ?_
  rw [WP.block_append_iff]
  have a0₆ : s₆.gpr .a0 = St + BitVec.ofNat 64 400 := by rw [x₆.gpr _ (by decide) (by decide), a0₅]
  refine WP.mono (Bytes.xorBytes_ok (t := .t2) (u := .t3) (dst := .a0) (src := .t6) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [x₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), t6₄, x₆.rd, x₆.wr, u₅.rd, u₅.wr, rd₄, wr₄]
      exact in_wr (kIn i hi))
    (fun i hi => by rw [a0₆, x₆.wr, u₅.wr, wr₄]; exact cIn i hi)
    (by rw [a0₆, x₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), t6₄]; exact nsep dK)) fun s₇ x₇ => ?_
  -- The block enciphered.
  have fx₆ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s₄.mem s₆.mem := by
    have := x₆.frame; rwa [a0₅, u₅.mem] at this
  have fx₇ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s₆.mem s₇.mem := by
    have := x₇.frame; rwa [a0₆] at this
  have b₇ : Spec.Aes.bytesAt s₇.mem (St + BitVec.ofNat 64 400) 8 =
      Spec.Cmac.xor (Spec.Cmac.xor (Spec.Aes.bytesAt s₄.mem (St + BitVec.ofNat 64 400) 8)
        (Spec.Aes.bytesAt s₄.mem Mp 8)) (Spec.Aes.bytesAt s₄.mem Kp 8) := by
    have e₂ := xorBytes_bytes x₇
    have e₁ := xorBytes_bytes x₆
    rw [a0₆, x₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), t6₄] at e₂
    rw [a0₅, u₅.other _ (by decide), t5₄, u₅.mem] at e₁
    rw [e₂, e₁, Proof.Cmac.bytesAt_frame fx₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dK.symm) (by decide)]
  unfold ecbArgs mov
  refine wp_mv fun s₈ u₈ => wp_addi (imm := 400) (by decide) fun s₉ u₉ => ?_
  refine WP.cons (exec_li (show imm12 1 by decide)) (WP.block_nil ?_)
  have sp₉ : s₉.sp = s₀.sp := by
    rw [u₉.sp, u₈.sp, x₇.sp, x₆.sp, u₅.sp, sp₄]
  have g₉ : ∀ r ∈ preserved, s₉.gpr r = s₄.gpr r := fun r hr => by
    obtain ⟨-, -, h2, h3, -, -, -, -, ha0, ha1, -⟩ := preserved_ne r hr
    rw [u₉.other _ ha1, u₈.other _ ha0, x₇.gpr _ h2 h3, x₆.gpr _ h2 h3, u₅.other _ ha0]
  refine ⟨⟨?_, ?_, by simp [RegUpd.gpr_write], by decide, by decide, hw,
      by simp only [RegUpd.sp_write]; rw [sp₉]; exact hp.al, by simp only [RegUpd.sp_write]; rw [sp₉]; exact hp.sp,
      by simp only [RegUpd.sp_write]; rw [sp₉]; exact hp.stk_st,
      by simp only [RegUpd.wr_write]; rw [u₉.wr, u₈.wr, x₇.wr, x₆.wr, u₅.wr, wr₄]; exact stW⟩,
    fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a0 ≠ .a2 by decide)]; rw [u₉.other _ (by decide), u₈.gpr,
      x₇.gpr _ (by decide) (by decide), x₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), s1₄]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .a2 by decide)]; rw [u₉.gpr, u₈.other _ (by decide),
      x₇.gpr _ (by decide) (by decide), x₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), s1₄]
  · simp only [RegUpd.gpr_write_of_ne _ _ (preserved_ne r hr).2.2.2.2.2.2.2.2.2.2.1]; exact g₉ r hr
  · simp only [RegUpd.rd_write]; rw [u₉.rd, u₈.rd, x₇.rd, x₆.rd, u₅.rd]
  · simp only [RegUpd.wr_write]; rw [u₉.wr, u₈.wr, x₇.wr, x₆.wr, u₅.wr]
  · simp only [RegUpd.sp_write]; rw [u₉.sp, u₈.sp, x₇.sp, x₆.sp, u₅.sp]
  · simp only [RegUpd.mem_write]; rw [u₉.mem, u₈.mem]; exact fx₆.trans fx₇
  · simp only [RegUpd.mem_write]; rw [u₉.mem, u₈.mem, hMe, hKe]; exact b₇

/-- The memory regions `finish` writes before its copy to `out`, apart from
the saved registers and the schedule. -/
theorem finish_wp {s₀ : State} (h0 : finishRISCV64.pre s₀) :
    WP isa finish s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ finishRISCV64.post s₀ s' := by
  have hp := FPre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a2 = O at hp
  generalize s₀.gpr .a3 = S at hp
  generalize (s₀.gpr .a1).toNat = n at hp
  have hw := hp.wSt
  have hsw := hp.wS
  have hhl := Proof.CmacTripleDes.Stream.held_le n
  have stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have oW : (⟨O, 8⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have sW : (⟨S, 640⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (heldCode_wp hp.hn h₁.a1) fun s₂ h₂ => ?_)
  obtain ⟨t0₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := h₂
  refine WP.seq (wp_subi (imm := 8) (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have t1₃ : s₃.gpr .t1 = BitVec.ofNat 64 (held n) - BitVec.ofNat 64 8 := by rw [u₃.gpr, t0₂]
  have g₃ : ∀ r, r ≠ .t0 → r ≠ .t1 → s₃.gpr r = s₁.gpr r := fun r a b => by rw [u₃.other _ b, g₂ r a]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, h₁.wr]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, h₁.rd]
  have s1₃ : s₃.gpr .s1 = St := by rw [g₃ _ (by decide) (by decide), h₁.s1]
  have s2₃ : s₃.gpr .s2 = S := by rw [g₃ _ (by decide) (by decide), h₁.s2]
  -- The last block and its subkey.
  have hbr := branch_wp hhl s1₃ s2₃ (by rw [u₃.other _ (by decide), t0₂]) t1₃ (by rw [wr₃]; exact stW)
    (by rw [wr₃]; exact sW) hp.st_s
  refine WP.seq (WP.mono hbr fun s₄ h₄ => ?_)
  obtain ⟨Mp, Kp, t5b, t6b, -, -, hblk⟩ := h₄.blk
  rw [h₄.t5] at t5b
  rw [h₄.t6] at t6b
  subst t5b t6b
  have s1₄ : s₄.gpr .s1 = St := by rw [h₄.keep _ (by decide), s1₃]
  have wr₄ : s₄.wr = s₀.wr := by rw [h₄.wr, wr₃]
  have rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, rd₃]
  have cv : Region.Sub ⟨St + BitVec.ofNat 64 400, 8⟩ ⟨St, 416⟩ := Offset.sub_base St (by decide)
  have sp₄ : s₄.sp = s₀.sp := by rw [h₄.sp, u₃.sp, sp₂, h₁.sp]
  refine WP.seq (WP.mono (finXor_wp hp s1₄ wr₄ rd₄ sp₄ h₄.t5 h₄.t6) fun s₉ h₉ => ?_)
  have sp₉ : s₉.sp = s₀.sp := h₉.sp.trans sp₄
  refine WP.seq (WP.mono (ecb_call h₉.args) fun s₁₀ h₁₀ => ?_)
  have g₁₀ : ∀ r ∈ preserved, s₁₀.gpr r = s₄.gpr r := fun r hr => by rw [h₁₀.saved r hr, h₉.keep r hr]
  have s1₁₀ : s₁₀.gpr .s1 = St := by rw [g₁₀ _ (by decide), s1₄]
  have s3₁₀ : s₁₀.gpr .s3 = O := by rw [g₁₀ _ (by decide), h₄.keep _ (by decide), g₃ _ (by decide) (by decide), h₁.s3]
  have s2₁₀ : s₁₀.gpr .s2 = S := by rw [g₁₀ _ (by decide), h₄.keep _ (by decide), s2₃]
  have wr₁₀ : s₁₀.wr = s₀.wr := by
    rw [h₁₀.wr, h₉.wr, wr₄]
  have rd₁₀ : s₁₀.rd = s₀.rd := by
    rw [h₁₀.rd, h₉.rd, rd₄]
  have sp₁₀ : s₁₀.sp = s₀.sp := by rw [h₁₀.sp, sp₉]
  rw [finOut, WP.block_append_iff]
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t0) (src := .s1) (dst := .s3) (soff := 400) (doff := 0) (n := 8)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [rd₁₀, wr₁₀, s1₁₀]; exact in_wr ⟨_, stW, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [wr₁₀, s3₁₀]; exact ⟨_, oW, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi hc => by
      rw [s3₁₀, s1₁₀, BitVec.add_zero] at hc
      exact hp.st_o _ (Offset.contains_base _ (by omega) (by omega)) hc)) fun s₁₁ c₁₁ => ?_
  have s2₁₁ : s₁₁.gpr .s2 = S := by rw [c₁₁.gpr _ (by decide), s2₁₀]
  rw [restoreRegs, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s2) fun s₁₂ e => ?_
  subst e
  rw [s2₁₁]
  -- The saved registers, through the writes.
  have fO : Frame [⟨O, 8⟩] s₁₀.mem s₁₁.mem := by
    have := c₁₁.frame; rwa [s3₁₀, BitVec.add_zero] at this
  have f₁₀ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩] s₉.mem s₁₀.mem := by
    have := h₁₀.frame; rwa [sp₉] at this
  have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, m₂]
  have dSv (p : Reg × Nat) (hp' : p ∈ finSaved) (r : Region) (hr : r ∈ [⟨S + BitVec.ofNat 64 64, 8⟩,
      ⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩, ⟨O, 8⟩]) :
      (⟨sv S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    have hb := fin_bound p hp'
    have sub56 : Region.Sub ⟨sv S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 56⟩ := sv_sub S (by omega)
    have sub : Region.Sub ⟨sv S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 640⟩ := fun a ha =>
      Region.sub_prefix (by decide) a (sub56 a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (Offset.base_disjoint S (by decide) (by omega)).sub_left sub56
    · exact (hp.st_s.sub_left cv).symm.sub_left sub
    · exact hp.stk_s.symm.sub_left sub
    · exact hp.o_s.symm.sub_left sub
  have sv₁ : Spill.Saved (sv S) (finG s₀ S) finSaved s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv S) _
  rw [← m₃] at sv₁
  have sv₄ := sv₁.frame h₄.frame fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have sv₉ := sv₄.frame h₉.frame fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  have sv₁₀ := sv₉.frame f₁₀ fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)
  have sv₁₁ := sv₁₀.frame fO fun p hp' r hr => dSv p hp' r (by
    simp only [List.mem_singleton] at hr; subst hr; simp)
  rw [show finSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 finSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := finSaved) (B := sv S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₁₁) fun s₁₃ r₁₃ => ?_
  · have := fin_bound p hp'
    show InRegions (s₁₁.rd ++ s₁₁.wr) _ 8
    rw [c₁₁.rd, c₁₁.wr, rd₁₀, wr₁₀, hp.rd, hp.wr]
    exact ⟨⟨S, 640⟩, by simp, sv_contains S (by omega) (by decide)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : finG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₁₃.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r = .s1 ∨ r = .s2 ∨ r = .s3
    · left; rcases hv with rfl | rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0, c₁₁.gpr _ h0, g₁₀ r hr, h₄.keep r hr,
        g₃ r h0 (preserved_ne r hr).2.1, h₁.other r hr (fun e => hv (.inl e)) (fun e => hv (.inr (.inl e)))
          (fun e => hv (.inr (.inr e))), g₀ r h0]
  · rw [r₁₃.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₁₃.sp, RegUpd.sp_write, c₁₁.sp, sp₁₀]
  · intro key msg hr ha1 hlen
    rw [hp.a2]
    rw [hp.a0] at hr
    have hn : n = msg.length := by
      have := congrArg BitVec.toNat (hp.a1.symm.trans ha1)
      rwa [toNat_ofNat hp.hn, toNat_ofNat hlen] at this
    subst hn
    rw [r₁₃.mem, RegUpd.mem_write]
    -- The state on entry, through the saves and the padded block.
    have f₁ : Frame [⟨sv S, 32⟩] s₀.mem s₃.mem := by
      rw [m₃, h₁.mem]
      exact Spill.saveMem_frame_base (l := finSaved) (n := 32) fin_bound (by decide) s₀.mem (sv S) (finG s₀ S)
    have dSt : ∀ d k, d + k ≤ 416 → ∀ r ∈ [(⟨sv S, 32⟩ : Region)], (⟨St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
      fun d k hk r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := sv_sub S (d := 0) (n := 32) (by decide)
        rw [BitVec.add_zero] at this
        exact (hp.st_s.sub_left (Offset.sub_base St hk)).sub_right fun a ha =>
          Region.sub_prefix (by decide) a (this a ha)
    have st₃ : ∀ d k, d + k ≤ 416 → Spec.Aes.bytesAt s₃.mem (St + BitVec.ofNat 64 d) k =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) k := fun d k hk =>
      Proof.Cmac.bytesAt_frame f₁ (dSt d k hk) (by omega)
    have st₄ : Spec.Aes.bytesAt s₄.mem (St + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 400) 8 := by
      rw [Proof.Cmac.bytesAt_frame h₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left cv).sub_right (Offset.sub_base S (by decide))) (by decide), st₃ 400 8 (by decide)]
    have sch : Spec.TripleDes.scheduleAt s₉.mem St = Spec.TripleDes.scheduleAt s₀.mem St := by
      have d384 : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 8⟩ : Region)], (⟨St, 384⟩ : Region).Disjoint r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint St (by decide) (by omega)
      rw [Proof.TripleDes.scheduleAt_eq_of_frame St h₉.frame d384,
        Proof.TripleDes.scheduleAt_eq_of_frame St h₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))),
        Proof.TripleDes.scheduleAt_eq_of_frame St f₁ (fun r hr => by
          have := dSt 0 384 (by decide) r hr; rwa [BitVec.add_zero] at this)]
    -- The MAC copied to `out`.
    have hout : Spec.Aes.bytesAt s₁₁.mem O 8 = Spec.Aes.bytesAt s₁₀.mem (St + BitVec.ofNat 64 400) 8 := by
      apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
      intro j h₁' _
      simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁'
      simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
      have := c₁₁.copied j h₁'
      rw [s3₁₀, s1₁₀, Nat.zero_add, ← Offset.add_add] at this
      exact this
    have hl8 : ∀ (m : Mem) (p : Addr), (Spec.Aes.bytesAt m p 8).length = 8 := fun _ _ => Proof.Cmac.bytesAt_length _ _ _
    rw [hout, h₁₀.out, h₉.out, xor_xor _ _ _ (by rw [hl8, hl8]) (by rw [hl8, hl8]), hblk, sch, st₄, st₃ 384 8 (by decide),
      st₃ 392 8 (by decide), st₃ 408 (held msg.length) (by omega)]
    exact finish_spec hr

end VG.Proof.CmacTripleDes.Stream.RISCV64
