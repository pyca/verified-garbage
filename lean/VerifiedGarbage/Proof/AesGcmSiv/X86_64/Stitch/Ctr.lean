module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Gh
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Chunk
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesGcmSiv.X86_64.Stitch.Loop`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.X86_64.Stitch.Aes`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV's interleaved loop: a batch of eight blocks

`batch_ok`: `batch j g` deciphers the eight data blocks at `rdx + 32 j`
(blocks `c … c + 7`, `AInv`): the counter blocks into `ymm3`–`ymm6`, as they
are (`ctrsR_ok`: the first 32-bit word, little-endian, advanced by `vpaddd`,
`ctrX`), AES of both lanes of each (`Vaes.aesG_ok`), whose bytes are
`CIPH_K` of the counter blocks' (`aesWith_le16`), and the XOR into the data
(`Vaes.xorData_ok`, on bytes by `bytes_of_blockAt`). The blocks `g i`
between the rounds do what `Q` says, as `Proof.Gcm.X86_64.Stitch.batch_ok`
states it.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.AesGcmSiv.X86_64Stitch (ctrsR batch)
open VG.Proof.Aes.X86_64.Vaes (aesG_ok xorData_ok two YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys st st_toList getD_st st_ext)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_rev pshufb_rev_xor)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr aregs_ok)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt)

/-! ## The counter blocks -/

/-- `vpaddd` of 2 in the first 32-bit word of each lane. -/
theorem paddd_two (a b c d : BitVec 32) :
    XBinOp.eval .paddd (ofDwords a b c d) two = ofDwords (a + BitVec.ofNat 32 2) b c d := by
  have h0 : dword two 0 = BitVec.ofNat 32 2 := by decide
  have h1 : dword two 1 = 0#32 := by decide
  have h2 : dword two 2 = 0#32 := by decide
  have h3 : dword two 3 = 0#32 := by decide
  simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, h0, h1, h2, h3,
    BitVec.add_zero]

theorem ctrX_two (icb : List Byte) (d : BitVec 128) (i : Nat) :
    XBinOp.eval .paddd (ctrX icb d i) two = ctrX icb d (i + 2) := by
  simp only [ctrX, paddd_two]
  rw [show Spec.GcmSiv.leNat (icb.take 4) + (i + 2) = Spec.GcmSiv.leNat (icb.take 4) + i + 2 by omega_arith,
    BitVec.ofNat_add (Spec.GcmSiv.leNat (icb.take 4) + i) 2]

/-- One register's two counter blocks into `b`. -/
theorem ctr1R_ok (c i b : XReg) (s : State) (icb : List Byte) (d : BitVec 128) (j : Nat) (hbc : b ≠ c)
    (hbi : b ≠ i) (hc : ∀ l < 2, s.lane c l = ctrX icb d (j + l)) (ht : ∀ l < 2, s.lane i l = two) :
    WP isa (.block [.vop (.vmovdqa .l256 b c), .vop (.vbin .vpaddd .l256 c c i)]) s fun s' =>
      (∀ l < 2, s'.lane b l = ctrX icb d (j + l)) ∧ (∀ l < 2, s'.lane c l = ctrX icb d (j + 2 + l)) ∧
      YFrame [b, c] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
  · rw [← hc l hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp [VOp.exec, State.lane_setV256, Ne.symm hbc, hbc]
  · have e : ((VOp.vmovdqa .l256 b c).exec s).lane c l = s.lane c l ∧
        ((VOp.vmovdqa .l256 b c).exec s).lane i l = s.lane i l := by
      rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [VOp.exec, State.lane_setV256, Ne.symm hbc, Ne.symm hbi]
    simp only [lane_vbin256, ite_true, e.1, e.2, hc l hl, ht l hl, VBinOp.sse, ctrX_two]
    exact congrArg _ (by omega_arith)
  · refine ⟨by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec], fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp [VOp.exec, State.lane_setV256, hr.1, hr.2]

theorem ctrsR_ok (c i : XReg) (hci : c ≠ i) (regs : List XReg) (s : State) (icb : List Byte) (d : BitVec 128)
    (j : Nat) (hnd : regs.Nodup) (hx : ∀ r ∈ regs, r ≠ c ∧ r ≠ i)
    (hc : ∀ l < 2, s.lane c l = ctrX icb d (j + l)) (ht : ∀ l < 2, s.lane i l = two) :
    WP isa (.block (ctrsR c i regs)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2, s'.lane regs[k] l = ctrX icb d (j + 2 * k + l)) ∧
      (∀ l < 2, s'.lane c l = ctrX icb d (j + 2 * regs.length + l)) ∧
      YFrame (c :: regs) s s' := by
  induction regs generalizing s j with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), fun l hl => by simpa using hc l hl,
      YFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨hbc, hbi⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrsR, WP.block_append_iff]
    refine WP.mono (ctr1R_ok c i b s icb d j hbc hbi hc ht) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (j + 2) (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      c₁ (fun l hl => by rw [f₁.lane _ (by simp [Ne.symm hbi, hci.symm]) l hl]; exact ht l hl))
      fun s' ⟨e, c', f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk l hl
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        rw [f.lane _ (by simp [hbc, hbs]) l hl, e₁ l hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk) l hl, show j + 2 + 2 * k + l = j + 2 * (k + 1) + l by omega_arith]
    · intro l hl
      rw [c' l hl, List.length_cons, show j + 2 + 2 * bs.length + l = j + 2 * (bs.length + 1) + l by omega_arith]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-- A counter block's bytes. -/
theorem le16_ctrX {icb : List Byte} {d : BitVec 128}
    (hrest : Proof.Cmac.le4 (dword d 1) ++ Proof.Cmac.le4 (dword d 2) ++ Proof.Cmac.le4 (dword d 3) = icb.drop 4)
    (i : Nat) : le16 (ctrX icb d i) = Spec.GcmSiv.counterBlock icb i := by
  rw [← bytesAt_writeW128 (fun _ => 0) 0 (ctrX icb d i)]
  exact counterBlock_store _ _ hrest

/-- The counter block at `cp s₀`, as it is. -/
abbrev d₀ (s₀ : State) : BitVec 128 := s₀.mem.readW (cp s₀) 128

theorem rest₀ (s₀ : State) :
    Proof.Cmac.le4 (dword (d₀ s₀) 1) ++ Proof.Cmac.le4 (dword (d₀ s₀) 2) ++ Proof.Cmac.le4 (dword (d₀ s₀) 3) =
      (icb s₀).drop 4 := by
  have h4 := Proof.Cmac.bytesAt_add s₀.mem (cp s₀) 4 12
  rw [show 4 + 12 = 16 from rfl] at h4
  rw [dword_readW _ _ (by decide), dword_readW _ _ (by decide), dword_readW _ _ (by decide), ← bytesAt_rest12]
  show _ = (bytesAt s₀.mem (cp s₀) 16).drop 4
  rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

theorem ctrX₀ (s₀ : State) : ctrX (icb s₀) (d₀ s₀) 0 = d₀ s₀ := by
  have h4 := Proof.Cmac.bytesAt_add s₀.mem (cp s₀) 4 12
  rw [show 4 + 12 = 16 from rfl] at h4
  have hw0 : dword (d₀ s₀) 0 = BitVec.ofNat 32 (Spec.GcmSiv.leNat ((icb s₀).take 4)) := by
    rw [dword_readW _ _ (by decide), show cp s₀ + BitVec.ofNat 64 (4 * 0) = cp s₀ from BitVec.add_zero _,
      GcmSiv.readW32_leNat]
    show _ = BitVec.ofNat 32 (Spec.GcmSiv.leNat ((bytesAt s₀.mem (cp s₀) 16).take 4))
    rw [h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
  rw [ctrX, Nat.add_zero, ← hw0]
  exact ofDwords_dword _

/-! ## AES and the data, as bytes -/

theorem le16_st (v : BitVec 128) : (st v).toList = le16 v := by
  rw [st_toList]; rfl

theorem st_le16 (v : BitVec 128) : (Vector.ofFn fun i : Fin 16 => (le16 v).getD i 0) = st v := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, VG.Proof.Aes.X86_64.AesNi.getD_ofFn hi]
  simp [le16, hi, byte]

/-- `CIPH_K` of the bytes of `x`, from the register `r` that AES of `x` left. -/
theorem aesWith_le16 (nr : Nat) (w : List Byte) (x r : BitVec 128) (h : st r = Spec.Aes.cipher nr w (st x)) :
    Spec.GcmSiv.aesWith nr w (le16 x) = le16 r := by
  rw [Spec.GcmSiv.aesWith, st_le16, ← h, le16_st]

/-- A block XORed with a byte-reversed register, as bytes. -/
theorem bytes_of_blockAt {m m' : Mem} {a : Addr} {r : BitVec 128}
    (h : blockAt m' a = blockAt m a ^^^ XBinOp.eval .pshufb r revMask) :
    bytesAt m' a 16 = Spec.Cmac.xor (bytesAt m a 16) (le16 r) := by
  have e : m'.readW a 128 = m.readW a 128 ^^^ r := by
    have := congrArg (fun v => XBinOp.eval .pshufb v revMask) h
    simp only [blockAt_eq, pshufb_rev_xor, pshufb_rev_rev] at this
    exact this
  rw [← le16_readW, ← le16_readW, e, le16_xor]

/-! ## A batch -/

/-- The decipherment after `c` blocks: the counter pair, the mask, the
increment, the key schedule and its last round key, and the data (blocks
below `c` deciphered, the others as they were). -/
structure AInv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  ctr : ∀ l < 2, s.lane .xmm14 l = ctrX (icb s₀) (d₀ s₀) (c + l)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = two
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [dR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < nb s₀, bytesAt s.mem (bAddr s₀ k) 16 = if k < c then ctb s₀ k else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : AInv s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : AInv s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.lane _ h14 l hl]; exact h.ctr l hl, fun l hl => by rw [f.lane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.lane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi,
    by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame, fun k hk => by rw [f.mem]; exact h.blocks k hk,
    by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

/-- The key schedule is not in the data or the working space. -/
theorem sch_frame {s₀ : State} (hp : SPre s₀) {m : Mem} (hf : Frame [dR s₀, pR s₀] s₀.mem m) :
    bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [sch, bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega_arith) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.d_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : AInv s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, sch_frame hp hI.frame], by rcases hp.rounds with h | h | h <;> omega_arith,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega_arith)⟩

theorem batch_ok {s₀ : State} (hp : SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨bAddr s₀ c, 128⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 8 ≤ nb s₀) {s : State} (hI : AInv s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 32 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => AInv s₀ (c + 8) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨bAddr s₀ c, 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hw := hp.wrap_d
  refine WP.seq (WP.mono (ctrsR_ok .xmm14 .xmm15 (by decide) aregs s (icb s₀) (d₀ s₀) c hnd
    (fun r h => ⟨(hx r h).1, (hx r h).2.2⟩) hI.ctr hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := YFrame.of_keys (hI.keys hp) f₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesG_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => ⟨(hG r h).1, (hG r h).2.1⟩) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 2, le16 (s₂.lane aregs[k] l) =
      ciph s₀ (Spec.GcmSiv.counterBlock (icb s₀) (c + 2 * k + l)) := fun k h l hl => by
    rw [← le16_ctrX (rest₀ s₀), ← e₁ k h l hl]
    exact (aesWith_le16 _ _ _ _ (e₂ _ (List.getElem_mem h) l hl)).symm
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, f₁.gpr]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (32 * j + 16 * i) = bAddr s₀ (c + i) := fun i =>
    addr_eq (by omega_arith)
  refine WP.mono (xorData_ok .xmm13 .rdx aregs j s₂ hnd h13 (fun k hk => by
      rw [hrdx₂, f₂.wr, f₁.wr, hI.wr, show BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int) =
        BitVec.ofNat 64 (32 * j + 16 * (2 * k)) by rw [BitVec.ofInt_natCast]; congr 1; omega_arith, addr]
      exact in_sub hp.d_in (by simp [aregs] at hk; omega_arith))
      (by rw [hrdx₂]; simp [aregs]; omega_arith))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hrdx₂] at b₃ fr₃
  rw [show 32 * j = 32 * j + 16 * 0 by omega_arith, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 2,
      bytesAt s₃.mem (bAddr s₀ (c + (2 * k + l))) 16 =
        Spec.Cmac.xor (bytesAt s.mem (bAddr s₀ (c + (2 * k + l))) 16) (le16 (s₂.lane aregs[k] l)) :=
    fun k h l hl => by
      have := b₃ k h l hl
      rw [show 16 * (2 * (j + k) + l) = 32 * j + 16 * (2 * k + l) by omega_arith, addr] at this
      exact bytes_of_blockAt this
  have fr' : Frame [⟨bAddr s₀ c, 128⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.lane r (by simp [h13', hr, hg']) l hl, f₁.lane r (by simp [h14, hr]) l hl]
  refine ⟨⟨by omega_arith, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [g₃, f₂.gpr, f₁.gpr, hI.rdi],
    by rw [g₃, f₂.gpr, f₁.gpr, hI.rsi], by rw [g₃, f₂.gpr, f₁.gpr, hI.r10], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    by rw [g₃, f₂.gpr, f₁.gpr], kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.lane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.2 rfl) l hl, hI.inc l hl]
  · -- The data written is only in the data.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨dR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 8) ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 8) → bytesAt s₃.mem (bAddr s₀ k) 16 = bytesAt s.mem (bAddr s₀ k) 16 :=
      fun hn => Proof.AesGcm.X86_64.bytesAt_frame fr' (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw hk hc hn h₁ h₂) (by decide)
    by_cases hlo : k < c
    · rw [out (by omega_arith), hI.blocks k hk]
      simp only [hlo, show k < c + 8 by omega_arith, ite_true]
    · by_cases hhi : k < c + 8
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega_arith⟩
        have hj : i / 2 < aregs.length := by simp [aregs]; omega_arith
        rw [hb3 (i / 2) hj (i % 2) (by omega_arith), hI.blocks _ hk, ks (i / 2) hj (i % 2) (by omega_arith),
          show c + 2 * (i / 2) + i % 2 = c + (2 * (i / 2) + i % 2) by omega_arith]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega_arith), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.AesGcmSiv.X86_64.Stitch

end

end

/-! ### `AesGcmSiv.X86_64.Stitch.Group`, which only this module used -/

section

/-!
# AES-GCM-SIV's interleaved loop: hashing a group between the rounds

`GEnv`: what the POLYVAL loads of a group need: its blocks at `rdx` (those
from `lo` on, which the loads to come read), as they are, and the powers in
the working space. `ghStep` is one load (`ghLoad_ok`), `ghFin` the reduction
of both lanes and their sum into `Y`. `QG` is what holds before the blocks
after round `j` of a batch, and `gq_ok` is `batch_ok`'s obligation for the
loads `gq base fin` place between the rounds, as for AES-GCM
(`Proof/Gcm/X86_64/Stitch/Group.lean`, whose products `accN` and `FinOk`
this uses).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (reduce_lanes combine_ok)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordE)
open VG.Impl.AesGcmSiv.X86_64Stitch (ghLoad gq)
open VG.Proof.Gcm.X86_64.Stitch (accN accN_succ off2 offp ite_t ite_f yNew FinOk gRegs gRegs_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Gcm (Block)

structure GEnv (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → Block) (P : Nat → Nat → Block) (s : State) :
    Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = pp s₀
  xs : ∀ i, lo ≤ i → i < 16 → s.mem.readW (a + BitVec.ofNat 64 (16 * i)) 128 = X i
  pv : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  ina : ∀ k < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32
  inp : ∀ k < 8, InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32

theorem GEnv.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {s : State} (h : GEnv s₀ lo a X P s) (hl : lo ≤ lo') : GEnv s₀ lo' a X P s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv.yframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {s s' : State} {rs : List XReg} (h : GEnv s₀ lo a X P s) (f : YFrame rs s s') : GEnv s₀ lo a X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun k hk l hl => by rw [f.mem]; exact h.pv k hk l hl, fun k hk => by rw [f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by rw [f.rd, f.wr]; exact h.inp k hk⟩

/-- One GHASH load, the `n`-th of the order `ord`. -/
theorem ghStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {ord : Nat → Nat} {n : Nat} (hk : ord n < 8) (hlo : lo ≤ 2 * ord n) {s : State}
    (hE : GEnv s₀ lo a X P s) (hp : ∀ l < 2, prod (s.proj l) = accN ord X P yl l n)
    (hy : ∀ l < 2, s.lane .xmm2 l = yl l) :
    WP isa (.block (ghLoad (ord n))) s fun s' => GEnv s₀ lo a X P s' ∧
      (∀ l < 2, prod (s'.proj l) = accN ord X P yl l (n + 1)) ∧ (∀ l < 2, s'.lane .xmm2 l = yl l) ∧
      YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  refine WP.mono (ghLoad_ok hk s (by rw [hE.rdx]; exact hE.ina _ hk) (by rw [hE.r11]; exact hE.inp _ hk))
    fun s' ⟨p', f'⟩ => ⟨hE.yframe f', fun l hl => ?_, fun l hl => ?_, f'⟩
  · rw [p' l hl, hp l hl, accN_succ, hE.rdx, hE.r11, off2, offp, hE.xs _ (by omega_using [hlo]) (by omega_using [hk, hl]),
      hE.pv _ hk l hl, hy l hl]
    rfl
  · rw [f'.lane _ (by decide) l hl, hy l hl]

/-- The reduction of both lanes, and their sum into `xmm2`. -/
theorem ghFin {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block} {s : State}
    (hE : GEnv s₀ lo a X P s) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Vpclmul.reduce .xmm7 ++ Impl.Gcm.X86_64.Vpclmul.combine)) s fun s' =>
      GEnv s₀ lo a X P s' ∧ s'.lane .xmm2 0 = reduce (prod (s.proj 0)) ^^^ reduce (prod (s.proj 1)) ∧
      s'.lane .xmm2 1 = 0 ∧ YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (reduce_lanes s h1) fun s₁ ⟨r₁, f₁⟩ => WP.mono (combine_ok s₁) fun s' ⟨c', y', f'⟩ =>
    ⟨(hE.yframe f₁).yframe f', by rw [c', r₁ 0 (by decide), r₁ 1 (by decide)], y',
      f₁.comp f'⟩

/-! ## The GHASH work of a batch -/

/-- What holds before the blocks after round `j` of a batch. -/
def QG (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → Block) (P : Nat → Nat → Block)
    (yl : Nat → Block) (ord : Nat → Nat) (base : Nat) (fin : Bool) (j : Nat) (s : State) : Prop :=
  GEnv s₀ (lo j) a X P s ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
  (if fin ∧ 5 < j then s.lane .xmm2 0 = yNew ord X P yl ∧ s.lane .xmm2 1 = 0
   else (∀ l < 2, prod (s.proj l) = accN ord X P yl l (base + min (j - 1) 4)) ∧
     ∀ l < 2, s.lane .xmm2 l = yl l)

theorem QG.yframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j : Nat} {s s' : State} {rs : List XReg}
    (h : QG s₀ lo a X P yl ord base fin j s) (f : YFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    QG s₀ lo a X P yl ord base fin j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  obtain k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r hr l hl => f.lane r (fun h => hrs r h hr) l hl
  obtain kp : ∀ l < 2, prod (s'.proj l) = prod (s.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, k .xmm8 (by decide) l hl, k .xmm9 (by decide) l hl,
      k .xmm10 (by decide) l hl]
  refine ⟨hE.yframe f, fun l hl => by rw [k .xmm1 (by decide) l hl]; exact h1 l hl,
    ?_⟩
  split
  · rw [ite_t (by assumption)] at h2
    exact ⟨by rw [k .xmm2 (by decide) 0 (by decide)]; exact h2.1, by rw [k .xmm2 (by decide) 1 (by decide)]; exact h2.2⟩
  · rw [ite_f (by assumption)] at h2
    exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl, fun l hl => by rw [k .xmm2 (by decide) l hl]; exact h2.2 l hl⟩

/-- `batch_ok`'s obligation for the GHASH work between the rounds. -/
theorem gq_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block}
    {yl : Nat → Block} {base : Nat} {fin : Bool}
    (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd : ∀ j, 1 ≤ j → j ≤ 4 → ordE (base + j - 1) < 8 ∧ lo j ≤ 2 * ordE (base + j - 1))
    (hfin : fin = true → base = 4) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → QG s₀ lo a X P yl ordE base fin j s →
      WP isa (.block (gq base fin j)) s fun s' =>
        QG s₀ lo a X P yl ordE base fin (j + 1) s' ∧ YFrame gRegs s s' := by
  intro j hj1 hj9 s _ ⟨hE, h1, h2⟩
  by_cases hl4 : j ≤ 4
  · -- A load.
    obtain ⟨hk, hlo⟩ := hrd j hj1 hl4
    rw [ite_f (by omega_using [hl4])] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega_using [hl4]] at h2
    obtain hn : base + (j - 1) = base + j - 1 := by omega_using [hj1]
    rw [hn] at h2
    refine WP.mono (ghStep hk hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
        f'.mono (by decide)⟩
    rw [ite_f (by omega_using [hl4]), show min (j + 1 - 1) 4 = j by omega_using [hl4], show base + j = base + j - 1 + 1 by omega_using [hj1]]
    exact ⟨p', y'⟩
  · by_cases h5 : fin = true ∧ j = 5
    · -- The reduction.
      obtain ⟨hf, rfl⟩ := h5
      rw [ite_f (by omega_using [])] at h2
      simp only [gq, show ¬ (1 ≤ 5 ∧ 5 ≤ 4) by omega_using [], ite_false, hf, and_self, ite_true]
      obtain hb := hfin hf
      subst hb
      refine WP.mono (ghFin hE h1) fun s' ⟨hE', y0, y1, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
          f'.mono (by decide)⟩
      rw [ite_t ⟨rfl, by omega_using []⟩]
      refine ⟨by rw [y0, h2.1 0 (by decide), h2.1 1 (by decide)]; rfl, y1⟩
    · -- Nothing.
      obtain hg : gq base fin j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega_using [hl4], ite_false]
        rw [ite_f h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, YFrame.refl _ _⟩
      by_cases hf : fin = true ∧ 5 < j
      · rw [ite_t hf] at h2; rw [ite_t ⟨hf.1, by omega_using [hl4]⟩]; exact h2
      · rw [ite_f hf] at h2
        by_cases hf' : fin = true ∧ 5 < j + 1
        · -- `j = 5` with `fin` is the reduction.
          have : ¬ 5 < j := fun h => hf ⟨hf'.1, h⟩
          exact absurd ⟨hf'.1, by omega_using [hl4, this]⟩ h5
        · rw [ite_f hf', show min (j + 1 - 1) 4 = min (j - 1) 4 by omega_using [hl4]]; exact h2

end VG.Proof.AesGcmSiv.X86_64.Stitch

end

end


/-!
# AES-GCM-SIV's interleaved loop: the body

`EInv s₀ P e s`: `e` groups of sixteen blocks are deciphered (`AInv`), the
plaintext of the first `e - 1` absorbed into `Y` (in `xmm2`), the powers `P`
in the working space; `rdx` points to group `e - 1`, the next to hash.
`body_ok`: a body deciphers group `e` (two batches, `batch_ok`) while it
hashes group `e - 1` between their rounds (`gq_ok`), which they do not write
(`QG.data`), as AES-GCM's encryption does (`Proof/Gcm/X86_64/Stitch/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs ordE)
open VG.Impl.AesGcmSiv.X86_64Stitch (batch gA gB body gq)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr FinOk gRegs gRegs_ok ite_t ite_f nextE_ok
  ghash_append16)
open VG.Proof.Aes.X86_64.AesNi (run_sep)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block ghashFrom)

/-- A block's 16 bytes, as POLYVAL's field element. -/
theorem readW_ofBytes (m : Mem) (a : Addr) : m.readW a 128 = Spec.GcmSiv.ofBytes (bytesAt m a 16) := by
  rw [GcmSiv.ofBytes_bytesAt, readW128_q]

/-! ## The POLYVAL state, kept by the data written -/

theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → Block}
    {P : Nat → Nat → Block} {yl : Nat → Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 8 ≤ nb s₀) (hg : 16 * g + 16 ≤ nb s₀) (ha : a.toNat = (dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 8))
    {t t' : State} (h : QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨bAddr s₀ c, 128⟩] t.mem t'.mem) : QG s₀ lo a X P yl ord base fin j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  obtain kp : ∀ l < 2, prod (t'.proj l) = prod (t.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) l hl, hlane .xmm9 (by decide) (by decide) l hl,
      hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    ⟩, fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega_using [ha])
    rw [e, hf.readW (r := ⟨bAddr s₀ (16 * g + i), 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega_using [hg, hi']) hc (hsep i hi hi') h₁ h₂) (by decide)]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega_using [hk, hl]) (by omega_using [hk, hl]))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega_using [hc]))) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        by rw [hlane _ (by decide) (by decide) 1 (by decide)]; exact h2.2⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-! ## The encryption loop -/

structure EInv (s₀ : State) (P : Nat → Nat → Block) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map fun k => Spec.GcmSiv.ofBytes (ctb s₀ k))
  y1 : s.lane .xmm2 1 = 0

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ nb s₀) {s : State} (hI : EInv s₀ P e s) :
    WP isa body s fun s' => EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => Spec.GcmSiv.ofBytes (ctb s₀ (16 * (e - 1) + i))
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  obtain hE₁ : GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          readW_ofBytes, hI.a.blocks _ (by omega_arith)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega_arith, ite_true]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith)) }
  obtain hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  obtain hrdx₁ : (s₁.gpr .rdx).toNat + 32 * 8 = (dp s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega_arith
  obtain hsepA : ∀ c, 16 * e ≤ c → ∀ i, 0 ≤ i → i < 16 → ¬ (c ≤ 16 * (e - 1) + i ∧ 16 * (e - 1) + i < c + 8) :=
    fun c hc i _ hi => by omega_arith
  -- The first batch, with loads 1–4 of the previous group.
  refine WP.seq (WP.mono (batch_ok hp gA gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 0 false)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega_arith) (by omega_arith) ha (hsepA _ (Nat.le_refl _)) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 8) (by omega_arith) hA₁ hrdx₁
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  obtain hrdx₂ : (s₂.gpr .rdx).toNat + 32 * 12 = (dp s₀).toNat + 16 * (16 * e + 8) := by
    rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega_arith
  obtain hQ₂' : QG s₀ (fun _ => 0) a X P yl ordE 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [ite_f (by decide)]; exact h2⟩
  -- The second batch, with loads 5–7 and 0 of the previous group, and the reduction.
  refine WP.seq (WP.mono (batch_ok hp gB gRegs gRegs_ok (QG s₀ (fun _ => 0) a X P yl ordE 4 true)
    (gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega_arith : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega_arith) (by omega_arith) ha (hsepA _ (by omega_arith)) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 12) (by omega_arith) hA₂ hrdx₂ hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (nextE_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [ite_t ⟨rfl, by decide⟩] at h2
  -- The memory of the powers is kept.
  obtain dP : ∀ c, c + 8 ≤ nb s₀ → ∀ r' ∈ [(⟨bAddr s₀ c, 128⟩ : Region)], (pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega_arith))
  obtain keepP : ∀ k < 8, ∀ l < 2, s'.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 =
      s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 :=
    fun k hk l hl => by
      rw [fm, hm₃.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide),
        hm₂.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide), f₁.mem]
  obtain gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  obtain lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (fun h => hg' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> decide)) l hl]
  obtain hA' : AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega_arith]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fm]; exact hA₃.frame,
      fun k hk => by rw [fm]; exact hA₃.blocks k hk, by rw [frd]; exact hA₃.rd, by rw [fwr]; exact hA₃.wr⟩
  obtain hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1; omega_arith
  refine ⟨⟨hA', by omega_arith, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [keepP k hk l hl]; exact hI.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega_arith)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega_arith, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega_arith, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega_arith), show e + 1 - 1 = e by omega_arith]

end VG.Proof.AesGcmSiv.X86_64.Stitch

end

end

/-! ### `AesGcmSiv.X86_64.Stitch.Enc`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV's interleaved loop: from the setup on

`Ready s₀ P s`: after the setup, nothing is deciphered (`AInv s₀ 0`), the
powers `P` are in the working space, `Y` in `xmm2`, `rdx` points to the data
(`setupT_ok`, after the powers are computed, which `Stitch/Ok.lean` proves in
the field). `first_ok`: the first group is deciphered (`EInv s₀ P 1`).
`decTail_ok`: the loop after the setup, for any powers whose products add up
to `GHASH` (`FinOk`), as AES-GCM's encryption (`Proof/Gcm/X86_64/Stitch/Enc.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs ordE)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupC first batch body ghLoad storeCtr lastG storeY)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Stitch (addr_eq in_sub in_sub_int in_rdwr FinOk accN storesK_ok pregs_get store16_ok
  ghash_append16)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

structure Ready (s₀ : State) (P : Nat → Nat → Block) (s : State) : Prop where
  a : AInv s₀ 0 s
  rdx : s.gpr .rdx = dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = y₀ s₀
  y1 : s.lane .xmm2 1 = 0

theorem pregs_get : ∀ k (h : k < pregs.length), pregs[k] = preg16 k := by decide

/-- Bytes outside the working space are kept by writes to it. -/
theorem bytesAt_outP {s₀ : State} {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame [pR s₀] m m')
    (hd : Region.Disjoint ⟨p, n⟩ (pR s₀)) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hn

theorem blockAt_outP {s₀ : State} {m m' : Mem} {p : Addr} (hf : Frame [pR s₀] m m')
    (hd : Region.Disjoint ⟨p, 16⟩ (pR s₀)) : blockAt m' p = blockAt m p :=
  Proof.AesGcm.X86_64.blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

theorem readW_outP {s₀ : State} {m m' : Mem} {p : Addr} (hf : Frame [pR s₀] m m')
    (hd : Region.Disjoint ⟨p, 16⟩ (pR s₀)) : m'.readW p 128 = m.readW p 128 :=
  hf.readW (r := ⟨p, 16⟩) (Region.contains_self _ _)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)

/-- The setup after the powers (`setupG`): they are stored in the working
space, then `Y`, the counter, the increment and the pointers. -/
theorem setupT_ok {s₀ : State} (hp : SPre s₀) {s₁ : State} (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask)
    (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly) (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem)
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupC)) s₁ (Ready s₀ fun k l => s₁.lane (preg16 k) l) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  obtain hr11 : s₁.gpr .r11 = pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact in_sub_int hp.p_in (by simp [pregs] at hk; omega_arith))
    (by rw [hr11]; simp [pregs]; omega_arith)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  replace fr : Frame [pR s₀] s₀.mem s₂.mem := fr.sub fun r hr => ⟨pR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  obtain hp₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → blockAt s₂.mem p = blockAt s₀.mem p :=
    fun hd => by rw [blockAt_outP fr hd]
  obtain hpw₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → s₂.mem.readW p 128 = s₀.mem.readW p 128 :=
    fun hd => by rw [readW_outP fr hd]
  obtain hpb₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (pR s₀) → bytesAt s₂.mem p 16 = bytesAt s₀.mem p 16 :=
    fun hd => by rw [bytesAt_outP fr hd (by decide)]
  refine WP.mono (setupC_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c140, c141, c15, r10, rax, rdx, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  obtain gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, c15, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_⟩,
    by rw [rdx, gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 => by rw [gk r h1 h2 h3, gs r h1], fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1⟩
  · have hd : s₂.mem.readW (s₂.gpr .rdx) 128 = d₀ s₀ := by rw [gs _ (by decide), hpw₂ hp.p_c.symm]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
    · rw [c140, hd, ctrX₀]
    · rw [c141, hd]
      conv => lhs; rw [← ctrX₀ s₀, ctrX, paddd_one, ← BitVec.ofNat_add]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [r10, gs _ (by decide), gs _ (by decide)]
  · rw [m₃]; exact fr.mono fun r hr => by simp at hr ⊢; exact Or.inr hr
  · rw [m₃, hpb₂ (hp.d_p.sub_left (Offset.sub_base _ (by omega_arith)))]
    simp only [Nat.not_lt_zero, ite_false]
  · rw [rd₃, rd₂, rd₁]
  · rw [wr₃, wr₂, wr₁]
  · rw [m₃, show pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega_arith) l hl, pregs_get]

/-- The first group: two batches, with nothing between their rounds. -/
theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} {s : State} (hR : Ready s₀ P s) :
    WP isa first s (EInv s₀ P 1) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega_arith) hR.a
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0 + 8) (j := 4) (by omega_arith) hA₁
    (by rw [hg₁, hR.rdx]) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_
  obtain dP : ∀ c, c + 8 ≤ nb s₀ → ∀ r' ∈ [(⟨bAddr s₀ c, 128⟩ : Region)], (pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega_arith))
  obtain lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ VG.Impl.Gcm.X86_64.Stitch.aregs → ∀ l < 2,
      s₂.lane r l = s.lane r l := fun r h13 h14 hr l hl => by
    rw [hl₂ r h13 h14 hr (by simp) l hl, hl₁ r h13 h14 hr (by simp) l hl]
  obtain gk : s₂.gpr = s.gpr := by rw [hg₂, hg₁]
  refine ⟨by simpa using hA₂, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, by rw [gk]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [gk]; exact hR.gpr r h1 h2 h4, fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    by rw [lk _ (by decide) (by decide) (by decide) 1 (by decide)]; exact hR.y1⟩
  · rw [gk, hR.gpr _ (by decide) (by decide) (by decide)]; simp
  · rw [hm₂.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide),
      hm₁.readW (r := pR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (dP _ (by omega_arith)) (by decide)]
    exact hR.pw k hk l hl

/-! ## The loop -/

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → Block} {e : Nat} {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      EInv s₀ P e s' ∧ s'.cf = some (decide (nb s₀ - 16 * (e - 1) < 32)) := by
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega_arith)]; rfl

theorem loopE_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {s : State}
    (hI : EInv s₀ P 1 s) (hcf : s.cf = some (decide (nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s' := by
  obtain fin : ∀ e, nb s₀ - 16 * (e - 1) < 32 → ∀ t, EInv s₀ P e t → ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega_arith, hI⟩
  refine WP.ite (decide (nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ EInv s₀ P e s
    obtain hstep : ∀ m s, I m s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ EInv s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (body_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          nb s₀ - 16 * (e + 1), by have := hI.one; omega_arith, e + 1, rfl, by omega_arith, hI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega_arith, hI⟩

/-! ## The last group, and the stores -/

/-- The loads `0 … n − 1` of the order of an encryption body. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → Block} {P : Nat → Nat → Block} {yl : Nat → Block} :
    ∀ n, n ≤ 8 → ∀ s, GEnv s₀ 0 a X P s → (∀ l < 2, prod (s.proj l) = Prod.zero) →
      (∀ l < 2, s.lane .xmm2 l = yl l) →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ordE i))) s fun s' => GEnv s₀ 0 a X P s' ∧
        (∀ l < 2, prod (s'.proj l) = accN ordE X P yl l n) ∧ (∀ l < 2, s'.lane .xmm2 l = yl l) ∧
        YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s'
  | 0, _, s, hE, hz, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, fun l hl => by rw [hz l hl]; rfl, hy, YFrame.refl _ _⟩
  | n + 1, hn, s, hE, hz, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ghRun_ok n (by omega_arith) s hE hz hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain hk : ordE n < 8 := by
      rcases (by omega_arith : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact WP.mono (ghStep hk (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ => ⟨hE', p', y', f₁.trans f'⟩

/-! ## The whole loop -/

/-- `vmovdqu [rax], xmm14`: the counter block stored, as it is. -/
theorem storeCtr_ok (s : State) (hin : InRegions s.wr (s.gpr .rax) 16) :
    WP isa (.block storeCtr) s fun s' => s'.mem = s.mem.writeW (s.gpr .rax) (s.lane .xmm14 0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l) := by
  obtain hin' : InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  apply WP.of_runBlock
  simp only [storeCtr, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin', ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.ofInt_natCast, BitVec.add_zero]; simp [State.lane], rfl, rfl, rfl, fun _ _ => rfl⟩

/-- A 16-byte write's frame. -/
theorem frame_write16 (m : Mem) (p : Addr) (v : BitVec 128) : Frame [⟨p, 16⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → Block} (hf : FinOk ordE (hk s₀) P) {e : Nat}
    (he : nb s₀ = 16 * e) {s : State} (hI : EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  obtain hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeCtr_ok s (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  -- The counter's memory is neither the data nor the working space.
  obtain cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_arith))
  obtain cP : ∀ k < 8, ∀ l < 2, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l), 16⟩ (cR s₀) :=
    fun k hk l hl => hp.p_c.sub_left (Offset.sub_base _ (by omega_arith))
  rw [hI.rax] at m₁
  obtain fC : Frame [cR s₀] s.mem s₁.mem := by rw [m₁]; exact frame_write16 _ _ _
  let a := s.gpr .rdx
  let X : Nat → Block := fun i => Spec.GcmSiv.ofBytes (ctb s₀ (16 * (e - 1) + i))
  let yl : Nat → Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (dp s₀).toNat + 256 * (e - 1) := hI.rdx
  obtain hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s₁) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  obtain hE₂ : GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega_arith),
          fC.readW (r := ⟨bAddr s₀ (16 * (e - 1) + i), 16⟩) (Region.contains_self _ _)
            (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact cD _ (by omega_arith)) (by decide),
          readW_ofBytes, hI.a.blocks _ (by omega_arith)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega_arith, ite_true]
        rfl
      pv := fun k hk l hl => by
        rw [f₂.mem, fC.readW (r := ⟨pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l), 16⟩) (Region.contains_self _ _)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact cP k hk l hl) (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            addr_eq (by omega_arith)]
        exact in_rdwr (in_sub hp.d_in (by omega_arith))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega_arith)) }
  rw [WP.block_append_iff]
  refine WP.mono (ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl, l₁]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  obtain hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [f₄.lane _ (by decide) 0 (by decide), f₃.lane _ (by decide) 0 (by decide),
      f₂.lane _ (by decide) 0 (by decide), l₁]; exact hm0
  obtain g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (store16_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  obtain hrcx : s.gpr .rcx = yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  obtain m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  -- The final memory: the counter, then `Y`, written.
  obtain fY : Frame [yR s₀] s₁.mem s₅.mem := by rw [m₅, ← m₁]; exact frame_write16 _ _ _
  obtain yD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hb : ∀ k < nb s₀, bytesAt s₅.mem (bAddr s₀ k) 16 = ctb s₀ k := fun k hk => by
    rw [Proof.AesGcm.X86_64.bytesAt_frame fY (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact yD k hk) (by decide),
      Proof.AesGcm.X86_64.bytesAt_frame fC (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cD k hk) (by decide),
      hI.a.blocks k hk]
    simp only [show k < 16 * e by omega_arith, ite_true]
  refine ⟨hb, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show bytesAt s₅.mem (cp s₀) 16 = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame fY (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.c_y) (by decide),
      m₁, bytesAt_writeW128, hI.a.ctr 0 (by decide), Nat.add_zero, he, le16_ctrX (rest₀ s₀)]
  · show blockAt s₅.mem (yp s₀) = _
    rw [m₅, VG.Proof.Gcm.X86_64.blockAt_store, y4]
    refine (hf X yl hI.y1).trans ?_
    rw [he, show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega_arith, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4

/-- The loop after the setup. -/
theorem decTail_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block}
    (hf : FinOk ordE (hk s₀) P) {s : State} (hR : Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (DPost s₀) := by
  refine WP.seq (WP.mono (first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (loopE_ok hp hm hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => final_ok hp hf he hI₄)

end VG.Proof.AesGcmSiv.X86_64.Stitch

end

end

/-!
# AES-GCM-SIV's sealing loops: counter mode on the groups

`ctr_ok`: `Impl.AesGcmSiv.X86_64Stitch.ctr` enciphers the `r9` blocks at
`r12` (a multiple of 16, at least 16) in counter mode from the counter block
at `rdx`, which it advances: the batches of `dec`, with nothing between their
rounds (`batch_ok`), sixteen blocks a body. It needs what the interleaved
loop needs (`SPre`) and leaves what it leaves but `Y` (`CPost`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupK cbody ctr batch storeCtr)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Gcm.X86_64.Stitch (in_rdwr)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Aes (bytesAt)

/-- `vinserti128 r, r, r, 1`: the low lane in both. -/
theorem insSelf_ok (r : XReg) (s : State) :
    WP isa (.block [.vop (.vinserti128 r r r 1)]) s fun s' =>
      (∀ l < 2, s'.lane r l = s.lane r 0) ∧ YFrame [r] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, fun r' hr l hl => ?_⟩⟩
  · rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [VOp.exec, State.setV, State.lane]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hr, VOp.exec, State.setV, State.lane]

/-- `setupK` after the mask. -/
abbrev setupKT : List Instr :=
  [.movImm64 .r10 1, .vop (.vmovq .xmm15 .r10),
   .vmovdquLoad .l128 .xmm14 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rdx 0),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm14 .xmm15), .vop (.vinserti128 .xmm14 .xmm14 .xmm13 1),
   .movImm64 .r10 2, .vop (.vmovq .xmm15 .r10), .vop (.vinserti128 .xmm15 .xmm15 .xmm15 1),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi),
   .mov .rax (.reg .rdx), .mov .rdx (.reg .r12)]

theorem setupKT_ok (s : State) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupKT) s fun s' =>
      s'.lane .xmm14 0 = s.mem.readW (s.gpr .rdx) 128 ∧
      s'.lane .xmm14 1 = XBinOp.eval .paddd (s.mem.readW (s.gpr .rdx) 128) ((0 : BitVec 64) ++ BitVec.ofNat 64 1) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r12 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  apply WP.of_runBlock
  simp only [setupKT, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun l hl => ?_, ?_, trivial, trivial, fun r h1 h2 h3 => ?_,
    fun r h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; rfl
  · rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h13, h14, h15]

/-- `add rdx, 256; sub r9, 16`. -/
theorem nextC_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.zf = some ((s.gpr .r9 - 16) == 0) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The counter loop's state: `e` groups enciphered. -/
structure CInv (s₀ : State) (e : Nat) (s : State) : Prop where
  a : AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r

theorem setupK_ok {s₀ : State} (hp : SPre s₀) : WP isa (.block setupK) s₀ (CInv s₀ 0) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  rw [show setupK = Impl.Gcm.X86_64.Pclmul.const .xmm0 revMask ++
    ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] : List Instr) ++ setupKT from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (insSelf_ok .xmm0 s₁) fun s₂ ⟨v₂, f₂⟩ => ?_
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [f₂.gpr, o₁.gpr r hr]
  have m₂ : s₂.mem = s₀.mem := by rw [f₂.mem, o₁.mem]
  refine WP.mono (setupKT_ok s₂ (by rw [f₂.wr, o₁.wr, g₂ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨c140, c141, c15, r10, rax, rdx, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have hd : s₂.mem.readW (s₂.gpr .rdx) 128 = d₀ s₀ := by rw [g₂ _ (by decide), m₂]
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, c15, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_⟩,
    by rw [rdx, g₂ _ (by decide), Nat.mul_zero, BitVec.add_zero],
    by rw [gk _ (by decide) (by decide) (by decide), g₂ _ (by decide), Nat.mul_zero, Nat.sub_zero]; simp,
    by rw [rax, g₂ _ (by decide)], fun r h1 h2 _ h4 => by rw [gk r h1 h2 h4, g₂ r h1]⟩
  · rcases (by omega_using [hl] : l = 0 ∨ l = 1) with rfl | rfl
    · rw [c140, hd, Nat.mul_zero, ctrX₀]
    · rw [c141, hd]
      conv => lhs; rw [← ctrX₀ s₀, ctrX, paddd_one, ← BitVec.ofNat_add]
  · rw [lk _ (by decide) (by decide) (by decide) l hl, v₂ l hl]; show s₁.xmm .xmm0 = _; rw [c₁]
  · rw [gk _ (by decide) (by decide) (by decide), g₂ _ (by decide)]
  · rw [gk _ (by decide) (by decide) (by decide), g₂ _ (by decide)]
  · rw [r10, g₂ _ (by decide), g₂ _ (by decide)]
  · rw [m₃, m₂]; exact Frame.refl _ _
  · rw [m₃, m₂]; simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]
  · rw [rd₃, f₂.rd, o₁.rd]
  · rw [wr₃, f₂.wr, o₁.wr]

theorem cbody_ok {s₀ : State} (hp : SPre s₀) {e : Nat} (he : 16 * (e + 1) ≤ nb s₀) {s : State}
    (hI : CInv s₀ e s) :
    WP isa cbody s fun s' => CInv s₀ (e + 1) s' ∧ s'.zf = some (decide (nb s₀ - 16 * (e + 1) = 0)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hw := hp.wrap_d
  have hrdx : (s.gpr .rdx).toNat = (dp s₀).toNat + 256 * e := by
    rw [hI.rdx, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 256 * e) (by omega_using [he, hw]),
      Nat.mod_eq_of_lt (by omega_using [he, hw])]
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * e) (j := 0) (by omega_using [he]) hI.a
    (by rw [hrdx]; omega_using []) trivial) fun s₁ ⟨hA₁, _, hg₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 16 * e + 8) (j := 4) (by omega_using [he]) hA₁
    (by rw [hg₁, hrdx]; omega_using []) trivial) fun s₂ ⟨hA₂, _, hg₂, _, _⟩ => ?_)
  refine WP.mono (nextC_ok s₂) fun s' ⟨frdx, fr9, fzf, fg, fl, fm, frd, fwr⟩ => ?_
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, hg₁]
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, hg₁, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega_using [he]) (by omega_using [hn])]
    congr 1
  refine ⟨⟨?_, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4⟩, ?_⟩
  · rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega_using []]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  · rw [frdx, hg₂, hg₁, hI.rdx, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, add_ofNat_assoc]
    congr 2
  · rw [fzf, hr9]
    simp only [Option.some.injEq]
    by_cases h : nb s₀ - 16 * (e + 1) = 0
    · simp [h]
    · simp only [h, decide_false]
      exact beq_false_of_ne fun h' => h (by
        have := congrArg BitVec.toNat h'
        rwa [toNat_ofNat_lt (by omega_using [hn])] at this)

/-- The counter block stored, and the upper lanes cleared. -/
theorem ctrFin_ok {s₀ : State} (hp : SPre s₀) {e : Nat} (he : nb s₀ = 16 * e) {s : State} (hI : CInv s₀ e s) :
    WP isa (.block (storeCtr ++ ([.vop .vzeroupper] : List Instr))) s (CPost s₀) := by
  have hw := hp.wrap_d
  rw [WP.block_append_iff]
  refine WP.mono (storeCtr_ok s (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [hI.rax] at m₁
  have fC : Frame [cR s₀] s.mem s₁.mem := by rw [m₁]; exact frame_write16 _ _ _
  have cD : ∀ k < nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega_using [hk]))
  refine ⟨fun k hk => ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, by show s₁.rd = _; rw [rd₁, hI.a.rd],
    by show s₁.wr = _; rw [wr₁, hI.a.wr]⟩
  · show bytesAt s₁.mem _ 16 = _
    rw [Proof.AesGcm.X86_64.bytesAt_frame fC (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cD k hk) (by decide),
      hI.a.blocks k hk]
    simp only [show k < 16 * e by omega_using [he, hk], ite_true]
  · show bytesAt s₁.mem (cp s₀) 16 = _
    rw [m₁, bytesAt_writeW128, hI.a.ctr 0 (by decide), Nat.add_zero, he, le16_ctrX (rest₀ s₀)]
  · show Frame _ s₀.mem s₁.mem
    rw [m₁]
    exact (hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)
  · show s₁.gpr r = _
    rw [g₁]; exact hI.gpr r h1 h2 h3 h4

/-- Counter mode on the groups. -/
theorem ctr_ok {s₀ : State} (hp : SPre s₀) (hm : nb s₀ % 16 = 0) : WP isa ctr s₀ (CPost s₀) := by
  have h16 := hp.nb16
  refine WP.seq (WP.mono (setupK_ok hp) fun s₁ hI₁ => WP.seq ?_)
  let I : Nat → State → Prop := fun m s => ∃ e, m = nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ nb s₀ ∧ CInv s₀ e s
  have hstep : ∀ m s, I m s → WP isa cbody s (fun s' =>
      (eval .ne s' = some false ∧ ∃ e, nb s₀ = 16 * e ∧ CInv s₀ e s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (cbody_ok hp he hI) fun s' ⟨hI', hzf⟩ => ?_
    by_cases h0 : nb s₀ - 16 * (e + 1) = 0
    · exact .inl ⟨by simp only [eval, hzf, h0, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega_using [he, h0], hI'⟩
    · exact .inr ⟨by simp only [eval, hzf, h0, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - 16 * (e + 1), by omega_using [he], e + 1, rfl, by omega_using [hm, h0], hI'⟩
  exact WP.mono (WP.loop (M := isa) I hstep (nb s₀ - 16 * 0) s₁ ⟨0, rfl, by omega_using [h16], hI₁⟩)
    fun s ⟨e, he, hI⟩ => ctrFin_ok hp he hI

end VG.Proof.AesGcmSiv.X86_64.Stitch
