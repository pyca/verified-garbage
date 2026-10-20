module

public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Chunk
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

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
  rw [show Spec.GcmSiv.leNat (icb.take 4) + (i + 2) = Spec.GcmSiv.leNat (icb.take 4) + i + 2 by omega,
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
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
      simp [VOp.exec, State.lane_setV256, Ne.symm hbc, hbc]
  · have e : ((VOp.vmovdqa .l256 b c).exec s).lane c l = s.lane c l ∧
        ((VOp.vmovdqa .l256 b c).exec s).lane i l = s.lane i l := by
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [VOp.exec, State.lane_setV256, Ne.symm hbc, Ne.symm hbi]
    simp only [lane_vbin256, ite_true, e.1, e.2, hc l hl, ht l hl, VBinOp.sse, ctrX_two]
    exact congrArg _ (by omega)
  · refine ⟨by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec], by simp [VOp.exec], fun r hr l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
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
        rw [e k (by simpa using hk) l hl, show j + 2 + 2 * k + l = j + 2 * (k + 1) + l by omega]
    · intro l hl
      rw [c' l hl, List.length_cons, show j + 2 + 2 * bs.length + l = j + 2 * (bs.length + 1) + l by omega]
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
  have hn : 16 * (nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [sch, bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.d_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : AInv s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, sch_frame hp hI.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

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
    addr_eq (by omega)
  refine WP.mono (xorData_ok .xmm13 .rdx aregs j s₂ hnd h13 (fun k hk => by
      rw [hrdx₂, f₂.wr, f₁.wr, hI.wr, show BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int) =
        BitVec.ofNat 64 (32 * j + 16 * (2 * k)) by rw [BitVec.ofInt_natCast]; congr 1; omega, addr]
      exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (by rw [hrdx₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hrdx₂] at b₃ fr₃
  rw [show 32 * j = 32 * j + 16 * 0 by omega, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 2,
      bytesAt s₃.mem (bAddr s₀ (c + (2 * k + l))) 16 =
        Spec.Cmac.xor (bytesAt s.mem (bAddr s₀ (c + (2 * k + l))) 16) (le16 (s₂.lane aregs[k] l)) :=
    fun k h l hl => by
      have := b₃ k h l hl
      rw [show 16 * (2 * (j + k) + l) = 32 * j + 16 * (2 * k + l) by omega, addr] at this
      exact bytes_of_blockAt this
  have fr' : Frame [⟨bAddr s₀ c, 128⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.lane r (by simp [h13', hr, hg']) l hl, f₁.lane r (by simp [h14, hr]) l hl]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [g₃, f₂.gpr, f₁.gpr, hI.rdi],
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
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + 8 by omega, ite_true]
    · by_cases hhi : k < c + 8
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega⟩
        have hj : i / 2 < aregs.length := by simp [aregs]; omega
        rw [hb3 (i / 2) hj (i % 2) (by omega), hI.blocks _ hk, ks (i / 2) hj (i % 2) (by omega),
          show c + 2 * (i / 2) + i % 2 = c + (2 * (i / 2) + i % 2) by omega]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.AesGcmSiv.X86_64.Stitch
