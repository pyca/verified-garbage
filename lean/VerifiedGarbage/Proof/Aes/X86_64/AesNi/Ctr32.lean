module

public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

section

/-!
# AES-NI counter mode: the counter blocks and the data

`ctrs_ok`: `ctrs regs` puts the counter blocks `CB`, `inc₃₂(CB)`, … into the
registers `regs`, as bytes; `xorData_ok`: `xorData regs j` XORs the registers
into the data blocks `j`, `j + 1`, …; both for any list of registers, by
induction.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ ctrs xorData dstReg)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-- `xmm11`: 1 in doubleword 0. -/
abbrev one : BitVec 128 := (0 : BitVec 64) ++ (1 : BitVec 64)

theorem paddd_one (c : Block) : XBinOp.eval .paddd c one = inc32 c := by
  have z : ∀ x : BitVec 32, x + 0 = x := fun x => BitVec.add_zero x
  have e0 : dword one 0 = 1 := by decide
  have e1 : dword one 1 = 0 := by decide
  have e2 : dword one 2 = 0 := by decide
  have e3 : dword one 3 = 0 := by decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, e0, e1, e2, e3, z, getLsbD_ofDwords, getLsbD_dword, inc32,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega_arith : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega_arith) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  first
  | rfl
  | exact congrArg _ (by omega_arith)

theorem rep_succ' {α : Type} (f : α → α) (a : α) : ∀ k, Nat.repeat f k (f a) = Nat.repeat f (k + 1) a
  | 0 => rfl
  | k + 1 => congrArg f (rep_succ' f a k)

theorem rep_add {α : Type} (f : α → α) (a : α) (i : Nat) :
    ∀ k, Nat.repeat f k (Nat.repeat f i a) = Nat.repeat f (i + k) a
  | 0 => rfl
  | k + 1 => congrArg f (rep_add f a i k)

/-- One counter block into `b`. -/
theorem ctr1_ok (b : XReg) (s : State) (h9 : b ≠ .xmm9) (h10 : b ≠ .xmm10) (h11 : b ≠ .xmm11)
    (hr : s.xmm .xmm10 = revMask) (ho : s.xmm .xmm11 = one) :
    WP isa (.block [.xop (.bin .movdqa b .xmm9), .xop (.bin .pshufb b .xmm10),
        .xop (.bin .paddd .xmm9 .xmm11)]) s fun s' =>
      s'.xmm b = XBinOp.eval .pshufb (s.xmm .xmm9) revMask ∧ s'.xmm .xmm9 = inc32 (s.xmm .xmm9) ∧
      XFrame [b, .xmm9] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, eval_movdqa, h9, Ne.symm h9, Ne.symm h10,
    Ne.symm h11, hr, ho, paddd_one,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

theorem ctrs_ok (regs : List XReg) (s : State) (hnd : regs.Nodup)
    (hx : ∀ r ∈ regs, r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm11)
    (hr : s.xmm .xmm10 = revMask) (ho : s.xmm .xmm11 = one) :
    WP isa (.block (ctrs regs)) s fun s' =>
      (∀ k (h : k < regs.length),
        s'.xmm regs[k] = XBinOp.eval .pshufb (Nat.repeat inc32 k (s.xmm .xmm9)) revMask) ∧
      s'.xmm .xmm9 = Nat.repeat inc32 regs.length (s.xmm .xmm9) ∧ XFrame (.xmm9 :: regs) s s' := by
  induction regs generalizing s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, XFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨h9, h10, h11⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (ctr1_ok b s h9 h10 h11 hr ho) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      (by rw [f₁.xmm _ (by simp [Ne.symm h10])]; exact hr)
      (by rw [f₁.xmm _ (by simp [Ne.symm h11])]; exact ho)) fun s' ⟨e, c, f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [f.xmm _ (by simp [h9, hbs]), e₁]; rfl
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk), c₁, rep_succ']
    · rw [c, c₁, rep_succ', List.length_cons]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-! ## The data -/

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem blockAt_writeW_sep (m : Mem) {p q : Addr} (v : BitVec 128) (h : Mem.Sep q 16 p 16) :
    blockAt (m.writeW p v) q = blockAt m q := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_sep h (by decide)]

/-- The block at `p` after writing to it the block at `q` XORed with `x`
(as bytes). -/
theorem blockAt_writeW_xorFrom (m : Mem) (p q : Addr) (x : BitVec 128) :
    blockAt (m.writeW p (XBinOp.eval .pxor x (m.readW q 128))) p =
      blockAt m q ^^^ XBinOp.eval .pshufb x revMask := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_self m p 16 _ (by decide), eval_pxor,
    pshufb_rev_xor, BitVec.xor_comm]

/-- The block at `p` after XORing `x` (as bytes) into it. -/
theorem blockAt_writeW_xor (m : Mem) (p : Addr) (x : BitVec 128) :
    blockAt (m.writeW p (XBinOp.eval .pxor x (m.readW p 128))) p =
      blockAt m p ^^^ XBinOp.eval .pshufb x revMask :=
  blockAt_writeW_xorFrom m p p x

/-- A block of a region disjoint from the frame's is unchanged. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : blockAt m' p = blockAt m p :=
  Proof.Gcm.blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem inRegions_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- XOR `b` into the block at `rcx + d`, stored at `D + d`. -/
theorem xor1_ok (b : XReg) (D : Reg) (d : Nat) (s : State) (hb8 : b ≠ .xmm8)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 16)
    (hin : InRegions s.wr (s.gpr D + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad .xmm8 (at_ .rcx d), .xop (.bin .pxor b .xmm8),
        .movdquStore (at_ D d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr D + BitVec.ofInt 64 (d : Int))
        (XBinOp.eval .pxor (s.xmm b) (s.mem.readW (s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm8 → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, State.store128, ea_at, hin, hinS, hb8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩

/-- `xorData regs j to`: the data blocks `j`, `j + 1`, … at `rcx` XORed with
the registers into the blocks at `dstReg to` (`D`), for any `D` the blocks
read after each store do not overlap that store (`hsep`). -/
theorem xorData_ok (to : Bool) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (h8 : .xmm8 ∉ regs)
    (hinS : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr (dstReg to) + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hw : (s.gpr (dstReg to)).toNat + 16 * (j + regs.length) ≤ 2 ^ 64)
    (hsep : ∀ i k, i < k → k < regs.length →
      Mem.Sep (s.gpr .rcx + BitVec.ofNat 64 (16 * (j + k))) 16
        (s.gpr (dstReg to) + BitVec.ofNat 64 (16 * (j + i))) 16) :
    WP isa (.block (xorData regs j to)) s fun s' =>
      (∀ k (h : k < regs.length), blockAt s'.mem (s.gpr (dstReg to) + BitVec.ofNat 64 (16 * (j + k))) =
        blockAt s.mem (s.gpr .rcx + BitVec.ofNat 64 (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.xmm regs[k]) revMask) ∧
      Frame [⟨s.gpr (dstReg to) + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm8 → r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : .xmm8 ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hinS hw hsep
    rw [xorData, WP.block_append_iff]
    have hin0 := hin 0 (by omega_arith)
    have hinS0 := hinS 0 (by omega_arith)
    rw [Nat.add_zero] at hin0 hinS0
    refine WP.mono (xor1_ok b (dstReg to) (16 * j) s hb8 hinS0 hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hD : s₁.gpr (dstReg to) = s.gpr (dstReg to) := by rw [g₁]
    have hS : s₁.gpr .rcx = s.gpr .rcx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8'
      (fun k hk => by
        rw [rd₁, wr₁, hS, show j + 1 + k = j + (k + 1) by omega_arith]; exact hinS (k + 1) (by omega_arith))
      (fun k hk => by
        rw [wr₁, hD, show j + 1 + k = j + (k + 1) by omega_arith]; exact hin (k + 1) (by omega_arith))
      (by rw [hD]; omega_arith)
      (fun i k hik hk => by
        rw [hD, hS, show j + 1 + k = j + (k + 1) by omega_arith, show j + 1 + i = j + (i + 1) by omega_arith]
        exact hsep (i + 1) (k + 1) (by omega_arith) (by omega_arith))) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hD, hS] at hb
    rw [hD] at hf
    have ofs : ∀ (p : Addr) (a : Nat), (p + BitVec.ofInt 64 (a : Int)) = p + BitVec.ofNat 64 a :=
      fun _ a => by rw [ofInt_natCast]
    rw [ofs, ofs] at m₁
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ r ∈ [(⟨s.gpr (dstReg to) + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr (dstReg to) + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [off_toNat _ _ (by omega_arith)] at h₁ h₂
      have := (a - s.gpr (dstReg to)).isLt
      omega_arith
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf hdj, m₁, blockAt_writeW_xorFrom]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hs0 := hsep 0 (k + 1) (by omega_arith) (by omega_arith)
        rw [Nat.add_zero] at hs0
        rw [show j + (k + 1) = j + 1 + k by omega_arith, hb k hk', m₁,
          blockAt_writeW_sep _ _ (by rw [show j + 1 + k = j + (k + 1) by omega_arith]; exact hs0),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk'))]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr (dstReg to) + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega_arith)] at ha ⊢
      have := (a - s.gpr (dstReg to)).isLt
      omega_arith
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2, x₁ r hr'.1 hr]

end VG.Proof.Aes.X86_64.AesNi

end

/-!
# AES-NI counter mode: the whole function

`ctr32_correct` and `ctr32_ct` prove `Impl.Aes.X86_64.AesNi.ctr32` against
`ctr32X86_64`, and `ctr32To_correct` and `ctr32To_ct` its out-of-place form
(`ctr32To`) against `ctr32ToX86_64`: one proof, for both store modes
(`to`), where the blocks are written to `dstReg to` (`dd`, the data itself in
place).
The loops keep, after `c` blocks, the counter block `inc₃₂ᶜ(CB)` in `xmm9` and
the first `c` blocks of the output written; the eight-block and one-block
bodies are the same code for different lists of registers (`blocks_ok`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ ctrs xorData dstReg dstStep aes regs8 body8 body1 ctrLoad ctrStore ctrTail
  ctr32T ctr32 ctr32To)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq blockAt_store)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev sp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev cp : Addr := s₀.gpr .rdx
abbrev dp : Addr := s₀.gpr .rcx
abbrev nb : Nat := (s₀.gpr .r8).toNat
abbrev sR : Region := ⟨sp s₀, 240⟩
abbrev cR : Region := ⟨cp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨s₀.gpr .r9, 2048⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (sp s₀) (16 * (nr s₀ + 1))
/-- `CIPH_K`. -/
abbrev ciph : Block → Block := aesWith (nr s₀) (sch s₀)
abbrev cb : Block := blockAt s₀.mem (cp s₀)
/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : Block := blockAt s₀.mem (bAddr s₀ k)

variable (to : Bool)

/-- The output: the data in place, or `r11`'s blocks out of place. -/
abbrev dd : Addr := s₀.gpr (dstReg to)
abbrev ddR : Region := ⟨dd s₀ to, 16 * nb s₀⟩
/-- Block `k` of the output. -/
abbrev oAddr (k : Nat) : Addr := dd s₀ to + BitVec.ofNat 64 (16 * k)

end

structure Pre (to : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = if to then [sR s₀, dR s₀] else [sR s₀]
  wr : s₀.wr = [cR s₀, ddR s₀ to, scrR s₀]
  s_c : (sR s₀).Disjoint (cR s₀)
  s_d : (sR s₀).Disjoint (ddR s₀ to)
  s_scr : (sR s₀).Disjoint (scrR s₀)
  c_d : (cR s₀).Disjoint (ddR s₀ to)
  c_scr : (cR s₀).Disjoint (scrR s₀)
  d_scr : (ddR s₀ to).Disjoint (scrR s₀)
  ret_c : (retR s₀).Disjoint (cR s₀)
  ret_d : (retR s₀).Disjoint (ddR s₀ to)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  /-- Out of place, the data and the output do not overlap. -/
  src : to = true → (dR s₀).Disjoint (ddR s₀ to)
  wrap : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrapD : (dd s₀ to).toNat + 16 * nb s₀ ≤ 2 ^ 64
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14

theorem pre_of (s₀ : State) (h : ctr32X86_64.pre s₀) : Pre false s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun h => Bool.noConfusion h, h12, h12, h13⟩

theorem preTo_of (s₀ : State) (h : ctr32ToX86_64.pre s₀) : Pre true s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, _, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h7, h8, h11, h12, h13, h14, fun _ => h9, h15, h16, h17⟩

namespace Pre
variable {to : Bool} {s₀ : State} (hp : Pre to s₀)
include hp

theorem keys (j : Nat) (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (sp s₀ + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 := by
  refine ⟨sR s₀, ?_, by rw [ofInt_natCast]; exact contains_offset (by omega_arith) (by omega_arith)⟩
  rw [hp.rd]; cases to <;> simp

/-- Block `k` is in the data. -/
theorem in_blk {k : Nat} (hk : k < nb s₀) : (dR s₀).Contains (bAddr s₀ k) 16 :=
  contains_offset (by omega_arith) (by have := hp.wrap; omega_arith)

/-- Block `k` of the output is in the output. -/
theorem in_out {k : Nat} (hk : k < nb s₀) : (ddR s₀ to).Contains (oAddr s₀ to k) 16 :=
  contains_offset (by omega_arith) (by have := hp.wrapD; omega_arith)

/-- Block `k` of the data can be read. -/
theorem src_blk {k : Nat} (hk : k < nb s₀) : InRegions (s₀.rd ++ s₀.wr) (bAddr s₀ k) 16 := by
  refine ⟨dR s₀, ?_, hp.in_blk hk⟩
  cases to with
  | false => rw [hp.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | true => rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem out_blk {k : Nat} (hk : k < nb s₀) : InRegions s₀.wr (oAddr s₀ to k) 16 :=
  ⟨ddR s₀ to, by rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self, hp.in_out hk⟩

/-- Memory that the output does not overlap. -/
theorem sch_frame {m : Mem} (hf : Frame [ddR s₀ to] s₀.mem m) :
    Spec.Aes.bytesAt m (sp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨sp s₀, 16 * (nr s₀ + 1)⟩) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.s_d.sub_left (Region.sub_prefix hn)) (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega_arith) hi

/-- Block `k` of the data does not overlap block `i` of the output, written
before it. -/
theorem sep_src {i k : Nat} (hk : k < nb s₀) (hik : i < k) :
    Mem.Sep (bAddr s₀ k) 16 (oAddr s₀ to i) 16 := by
  cases to with
  | true => exact (hp.src rfl).sep (hp.in_blk hk) (hp.in_out (by omega_arith))
  | false =>
    have hw := hp.wrap
    intro a h₁ h₂
    change (a - (dp s₀ + BitVec.ofNat 64 (16 * i))).toNat < 16 at h₂
    rw [off_toNat _ _ (by omega_arith)] at h₁ h₂
    have := (a - dp s₀).isLt
    omega_arith

/-- Block `k` of the data does not overlap the output out of place. -/
theorem src_disj {k : Nat} (hk : k < nb s₀) (ht : to = true) :
    ∀ r ∈ [ddR s₀ to], Region.Disjoint ⟨bAddr s₀ k, 16⟩ r := by
  simp only [List.mem_singleton, forall_eq]
  exact (hp.src ht).sub_left fun x hx =>
    (hp.in_blk hk).byte (by simp only [Region.Contains] at hx; omega_arith)

end Pre

/-! ## The loop invariant -/

/-- After `c` blocks, with `rcx`, `dstReg to` and `r8` at block `p`. -/
structure Inv (to : Bool) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  x9 : s.xmm .xmm9 = Nat.repeat inc32 c (cb s₀)
  x10 : s.xmm .xmm10 = revMask
  x11 : s.xmm .xmm11 = one
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → r ≠ dstReg to → s.gpr r = s₀.gpr r
  r10 : s.gpr .r10 = sp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  rcx : s.gpr .rcx = bAddr s₀ p
  r8 : s.gpr .r8 = BitVec.ofNat 64 (nb s₀ - p)
  dst : s.gpr (dstReg to) = oAddr s₀ to p
  frame : Frame [ddR s₀ to] s₀.mem s.mem
  blocks : ∀ k < nb s₀,
    blockAt s.mem (oAddr s₀ to k) = if k < c then blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀))
      else blockAt s₀.mem (oAddr s₀ to k)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The blocks of the data not yet read are as they were. -/
theorem Inv.src {to : Bool} {s₀ : State} {c p : Nat} {s : State} (hp : Pre to s₀) (hI : Inv to s₀ c p s)
    {k : Nat} (hk : k < nb s₀) (hck : c ≤ k) : blockAt s.mem (bAddr s₀ k) = blk s₀ k := by
  cases to with
  | false =>
    have := hI.blocks k hk
    simp only [show ¬ k < c by omega_arith, ↓reduceIte] at this
    exact this
  | true => exact blockAt_frame hI.frame (hp.src_disj hk rfl)

/-- `Inv.blocks` in place, about the data's blocks. -/
theorem Inv.blocksIn {s₀ : State} {c p : Nat} {s : State} (hI : Inv false s₀ c p s) :
    ∀ k < nb s₀, blockAt s.mem (bAddr s₀ k) =
      if k < c then blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀)) else blk s₀ k :=
  hI.blocks

theorem regs_nodup (rs : List XReg) (h : rs = regs8 ∨ rs = [.xmm0]) :
    rs.Nodup ∧ .xmm8 ∉ rs ∧ ∀ r ∈ rs, r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm11 := by
  rcases h with rfl | rfl <;> decide

/-- Blocks `c … c + n − 1` of a run are in it. -/
theorem run_in {d a : Addr} {nb c n : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hc : c + n ≤ nb)
    (ha : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : (a - d).toNat < 16 * nb := by
  rw [off_toNat _ _ (by omega_arith)] at ha
  have := (a - d).isLt
  omega_arith

/-- Block `k` of a run is not in blocks `c … c + n − 1`. -/
theorem run_sep {d a : Addr} {nb c n k : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hk : k < nb)
    (hc : c + n ≤ nb) (hn : ¬ (c ≤ k ∧ k < c + n))
    (h₁ : (a - (d + BitVec.ofNat 64 (16 * k))).toNat < 16)
    (h₂ : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : False := by
  rw [off_toNat _ _ (by omega_arith)] at h₁ h₂
  have := (a - d).isLt
  omega_arith

theorem dstReg_ne (to : Bool) : dstReg to ≠ .rdi ∧ dstReg to ≠ .rsi ∧ dstReg to ≠ .rdx ∧
    dstReg to ≠ .r8 ∧ dstReg to ≠ .r10 ∧ dstReg to ≠ .rax := by
  cases to <;> decide

/-- The counter blocks, AES and the XOR into the output, for the blocks
`c … c + N - 1` (`N` the number of registers). -/
theorem blocks_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) (rs : List XReg) (hrs : rs = regs8 ∨ rs = [.xmm0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ nb s₀) {s : State}
    (hI : Inv to s₀ c c s) (hQ : ∀ s', Inv to s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrs rs)) (.seq (aes rs) (.block (xorData rs 0 to ++ tail)))) s Q := by
  obtain ⟨hnd, h8, hx⟩ := regs_nodup rs hrs
  have hlen : 0 < rs.length := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.wrap
  have hwD := hp.wrapD
  refine WP.seq (WP.mono (ctrs_ok rs s hnd hx hI.x10 hI.x11) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  rw [hI.x9, rep_add] at c₁
  have ek : ∀ k (h : k < rs.length),
      s₁.xmm rs[k] = XBinOp.eval .pshufb (Nat.repeat inc32 (c + k) (cb s₀)) revMask := by
    intro k h; rw [e₁ k h, hI.x9, rep_add]
  have hrdi : s.gpr .rdi = s₀.gpr .rdi :=
    hI.gpr .rdi (by decide) (by decide) (by decide) (by decide) (dstReg_ne to).1.symm
  have hg₁ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → r ≠ dstReg to → s₁.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [f₁.gpr, hI.gpr r h1 h2 h3 h4 h5]
  have hK : Keys (nr s₀) (sch s₀) s₁ :=
    ⟨by rw [f₁.mem, f₁.gpr, hrdi, hp.sch_frame hI.frame],
      by rcases hp.rounds with h | h | h <;> omega_arith,
      fun j hj => by
        rw [f₁.rd, f₁.wr, f₁.gpr, hI.rd, hI.wr, hrdi]
        exact hp.keys j (by rcases hp.rounds with h | h | h <;> omega_arith)⟩
  refine WP.seq (WP.mono (aes_ok rs hnd h8 hp.rounds s₁ hK
    (by rw [hg₁ .rsi (by decide) (by decide) (by decide) (by decide) (dstReg_ne to).2.1.symm]; simp)
    (by rw [f₁.gpr, hI.r10, hrdi]))
    fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s₂.xmm rs[k]) revMask =
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := fun k h =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h), ek k h])).symm
  have hrcx₂ : s₂.gpr .rcx = bAddr s₀ c := by rw [f₂.gpr, f₁.gpr, hI.rcx]
  have hdst₂ : s₂.gpr (dstReg to) = oAddr s₀ to c := by rw [f₂.gpr, f₁.gpr, hI.dst]
  have hdstN : (s₂.gpr (dstReg to)).toNat = (dd s₀ to).toNat + 16 * c := by
    rw [hdst₂, oAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  have addrS : ∀ k, s₂.gpr .rcx + BitVec.ofNat 64 (16 * (0 + k)) = bAddr s₀ (c + k) :=
    fun k => by
      rw [hrcx₂, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega_arith]
  have addrD : ∀ k, s₂.gpr (dstReg to) + BitVec.ofNat 64 (16 * (0 + k)) = oAddr s₀ to (c + k) :=
    fun k => by
      rw [hdst₂, oAddr, oAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega_arith]
  have hrdwr : s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr := ⟨by rw [f₂.rd, f₁.rd, hI.rd], by rw [f₂.wr, f₁.wr, hI.wr]⟩
  rw [WP.block_append_iff]
  refine WP.mono (xorData_ok to rs 0 s₂ hnd h8
      (fun k hk => by rw [ofInt_natCast, addrS, hrdwr.1, hrdwr.2]; exact hp.src_blk (by omega_arith))
      (fun k hk => by rw [ofInt_natCast, addrD, hrdwr.2]; exact hp.out_blk (by omega_arith))
      (by rw [hdstN]; omega_arith)
      (fun i k hik hk => by rw [addrS, addrD]; exact hp.sep_src (by omega_arith) (by omega_arith)))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂] at b₃ fr₃
  rw [hdst₂, Nat.mul_zero, BitVec.add_zero] at fr₃
  simp only [addrS, addrD] at b₃
  have kx : ∀ r, r ≠ .xmm8 → r ≠ .xmm9 → r ∉ rs → s₃.xmm r = s.xmm r := fun r h8' h9 hr => by
    rw [x₃ r h8' hr, f₂.xmm r (by simp [h8', hr]), f₁.xmm r (by simp [h9, hr])]
  refine ⟨Nat.le_trans (by omega_arith) hc, ?_, ?_, ?_,
    fun r h1 h2 h3 h4 h5 => by rw [g₃, f₂.gpr, hg₁ r h1 h2 h3 h4 h5], ?_,
    by rw [g₃, hrcx₂], by rw [g₃, f₂.gpr, f₁.gpr, hI.r8], by rw [g₃, hdst₂], ?_, ?_,
    by rw [rd₃, hrdwr.1], by rw [wr₃, hrdwr.2]⟩
  · rw [x₃ _ (by decide) (fun h => (hx _ h).1 rfl), f₂.xmm _ (by
      simp only [List.mem_cons, not_or]; exact ⟨by decide, fun h => (hx _ h).1 rfl⟩), c₁]
  · rw [kx _ (by decide) (by decide) (fun h => (hx _ h).2.1 rfl), hI.x10]
  · rw [kx _ (by decide) (by decide) (fun h => (hx _ h).2.2 rfl), hI.x11]
  · rw [g₃, f₂.gpr, f₁.gpr, hI.r10]
  · -- The blocks written are only in the output.
    refine hI.frame.trans (fr₃.sub fun r hr => ⟨ddR s₀ to, List.mem_singleton_self _, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact run_in hwD hc ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + rs.length) →
        blockAt s₃.mem (oAddr s₀ to k) = blockAt s.mem (oAddr s₀ to k) :=
      fun hn => blockAt_frame fr₃ fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact run_sep hwD hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega_arith), hI.blocks k hk]
      simp only [hlo, show k < c + rs.length by omega_arith, ite_true]
    · by_cases hhi : k < c + rs.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega_arith⟩
        have hj : j < rs.length := by omega_arith
        rw [b₃ j hj, hI.src hp hk (by omega_arith), ks j hj]
        simp only [hhi, ite_true]
      · rw [out (by omega_arith), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem nb_lt {to : Bool} {s₀ : State} (hp : Pre to s₀) : 16 * nb s₀ ≤ 2 ^ 64 := by
  have := hp.wrap; omega_arith

/-- `dstReg to` and `rcx` on to block `c + n`, `r8` down to `nb - (c + n)`,
from `Inv` at `c + n` with them at `c`. -/
theorem step_inv {to : Bool} {s₀ : State} (hp : Pre to s₀) {c n : Nat} (hc : c + n ≤ nb s₀) {s₁ : State}
    (hI₁ : Inv to s₀ (c + n) c s₁) {s : State}
    (hg : ∀ r, r ≠ .rcx → r ≠ .r8 → r ≠ dstReg to → s.gpr r = s₁.gpr r)
    (hrcx : s.gpr .rcx = s₁.gpr .rcx + BitVec.ofNat 64 (16 * n))
    (hdst : s.gpr (dstReg to) = s₁.gpr (dstReg to) + BitVec.ofNat 64 (16 * n))
    (hr8 : s.gpr .r8 = s₁.gpr .r8 - BitVec.ofNat 64 n)
    (hx : s.xmm = s₁.xmm) (hm : s.mem = s₁.mem) (hrd : s.rd = s₁.rd) (hwr : s.wr = s₁.wr) :
    Inv to s₀ (c + n) (c + n) s := by
  have hn := nb_lt hp
  have hwD := hp.wrapD
  have hdr : dstReg to ≠ .rcx ∨ to = false := by cases to <;> simp [dstReg]
  refine { hI₁ with
    x9 := by rw [hx, hI₁.x9]
    x10 := by rw [hx, hI₁.x10]
    x11 := by rw [hx, hI₁.x11]
    gpr := fun r h1 h2 h3 h4 h5 => by rw [hg r h2 h3 h5, hI₁.gpr r h1 h2 h3 h4 h5]
    r10 := by rw [hg .r10 (by decide) (by decide) (dstReg_ne to).2.2.2.2.1.symm, hI₁.r10]
    rcx := by rw [hrcx, hI₁.rcx, bAddr, bAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
    r8 := by
      rw [hr8, hI₁.r8]
      have := (s₀.gpr .r8).isLt
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    dst := by rw [hdst, hI₁.dst, oAddr, oAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
    frame := by rw [hm]; exact hI₁.frame
    blocks := fun k hk => by rw [hm]; exact hI₁.blocks k hk
    rd := by rw [hrd, hI₁.rd]
    wr := by rw [hwr, hI₁.wr] }

/-- The eight-block body. -/
theorem body8_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {s : State}
    (hI : Inv to s₀ c c s) :
    WP isa (body8 to) s fun s' => Inv to s₀ (c + 8) (c + 8) s' ∧
      s'.cf = some (decide (nb s₀ - (c + 8) < 8)) := by
  have hn := nb_lt hp
  refine blocks_ok hp regs8 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hsub : s₁.gpr .r8 - 8 = BitVec.ofNat 64 (nb s₀ - (c + 8)) := by
    rw [hI₁.r8]; have := (s₀.gpr .r8).isLt; bv_omega
  cases to with
  | false =>
    apply WP.of_runBlock
    simp only [dstStep, Bool.false_eq_true, List.nil_append, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨step_inv hp hc hI₁ (fun r h1 h2 _ => by simp [h1, h2]) (by simp) (by simp [dstReg])
      (by simp) rfl rfl rfl rfl, ?_⟩
    simp only [hsub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show nb s₀ - (c + 8) < 2 ^ 64 by omega_arith), show (8 : BitVec 64).toNat = 8 from rfl]
  | true =>
    apply WP.of_runBlock
    simp only [dstStep, ↓reduceIte, List.cons_append, List.nil_append, reduceCtorEq, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg,
      e128, e8, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨step_inv hp hc hI₁ (fun r h1 h2 h3 => by simp [dstReg] at h3; simp [h1, h2, h3])
      (by simp) (by simp [dstReg]) (by simp) rfl rfl rfl rfl, ?_⟩
    simp only [hsub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show nb s₀ - (c + 8) < 2 ^ 64 by omega_arith), show (8 : BitVec 64).toNat = 8 from rfl]

/-- The one-block body. -/
theorem body1_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c : Nat} (hc : c < nb s₀) {s : State}
    (hI : Inv to s₀ c c s) :
    WP isa (body1 to) s fun s' => Inv to s₀ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (nb s₀ - (c + 1) = 0)) := by
  have hn := nb_lt hp
  refine blocks_ok hp [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hsub : s₁.gpr .r8 - 1 = BitVec.ofNat 64 (nb s₀ - (c + 1)) := by
    rw [hI₁.r8]; have := (s₀.gpr .r8).isLt; bv_omega
  cases to with
  | false =>
    apply WP.of_runBlock
    simp only [dstStep, Bool.false_eq_true, List.nil_append, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨step_inv hp hc hI₁ (fun r h1 h2 _ => by simp [h1, h2]) (by simp) (by simp [dstReg])
      (by simp) rfl rfl rfl rfl, ?_⟩
    rw [hsub, beq_ofNat_zero (by omega_arith)]
  | true =>
    apply WP.of_runBlock
    simp only [dstStep, ↓reduceIte, List.cons_append, List.nil_append, reduceCtorEq, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg,
      e16, e1, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨step_inv hp hc hI₁ (fun r h1 h2 h3 => by simp [dstReg] at h3; simp [h1, h2, h3])
      (by simp) (by simp [dstReg]) (by simp) rfl rfl rfl rfl, ?_⟩
    rw [hsub, beq_ofNat_zero (by omega_arith)]

/-! ## The prologue and the epilogue -/

theorem ctrLoad_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) :
    WP isa (.block ctrLoad) s₀ fun s => Inv to s₀ 0 0 s ∧ s.cf = some (decide (nb s₀ < 8)) := by
  have hin : InRegions (s₀.rd ++ s₀.wr) (cp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨cR s₀, by rw [hp.wr]; exact List.mem_append_right _ List.mem_cons_self,
      by rw [ofInt_natCast]; exact contains_offset (by omega_arith) (by omega_arith)⟩
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hd := dstReg_ne to
  apply WP.of_runBlock
  simp only [ctrLoad, Impl.Aes.X86_64.AesNi.const, List.cons_append, List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setXmm, State.setReg, State.load128,
    ea_at, hin, movq_const, e8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨Nat.zero_le _, ?_, rfl, rfl, fun r h1 h2 h3 h4 _ => by simp [h1, h4], ?_, ?_, ?_, ?_,
    Frame.refl _ _, fun k _ => by simp, rfl, rfl⟩, ?_⟩ <;>
    try simp only [reduceCtorEq, ↓reduceIte]
  · rw [ofInt_natCast]
    simp only [BitVec.add_zero]
    exact (blockAt_eq _ _).symm
  · simp only [nr, sp]; bv_omega
  · simp [bAddr]
  · simp [nb]
  · simp [hd.2.2.2.2.2, hd.2.2.2.2.1, oAddr, dd]
  · simp

theorem test_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c : Nat} {s : State} (hI : Inv to s₀ c c s) :
    WP isa (.block [.alu .test .r8 (.reg .r8)]) s fun s' =>
      Inv to s₀ c c s' ∧ s'.zf = some (decide (nb s₀ - c = 0)) := by
  have hn := nb_lt hp
  have hr8 := hI.r8
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hr8, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with }, by rw [beq_ofNat_zero (by omega_arith)]⟩

/-- What `vg_aes_ctr32_aesni` leaves, in place or out of place: the output
holds the data XORed with the keystream, and the counter block is advanced. -/
def Post (to : Bool) (s₀ s' : State) : Prop :=
  blocksAt s'.mem (dd s₀ to) (nb s₀) = Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (dp s₀) (nb s₀)) ∧
    blockAt s'.mem (cp s₀) = Nat.repeat inc32 (nb s₀) (cb s₀)

theorem ctrStore_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {s : State}
    (hI : Inv to s₀ (nb s₀) (nb s₀) s) :
    WP isa (.block ctrStore) s fun s' => gprPreserved s₀ s' ∧ Post to s₀ s' := by
  have hd := dstReg_ne to
  have hrdx : s.gpr .rdx = cp s₀ := hI.gpr .rdx (by decide) (by decide) (by decide) (by decide) hd.2.2.1.symm
  have hout : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨cR s₀, by rw [hI.wr, hp.wr]; exact List.mem_cons_self, by
      rw [hrdx, ofInt_natCast]; exact contains_offset (by omega_arith) (by omega_arith)⟩
  have h10 := hI.x10
  have h9 := hI.x9
  apply WP.of_runBlock
  simp only [↓reduceIte, ctrStore, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.setXmm, State.store128, ea_at, hout, h10, h9,
    Option.some.injEq, exists_eq_left']
  rw [hrdx, ofInt_natCast]
  simp only [BitVec.add_zero]
  have sep : ∀ {r : Region}, r.Disjoint (cR s₀) → ∀ {a : Addr} {n : Nat}, r.Contains a n →
      Mem.Sep a n (cp s₀) 16 := fun h _ _ ha => h.sep ha (Region.contains_self _ _)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h5 : r ≠ dstReg to := by
      cases to <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h5
  · rw [Mem.readW_writeW_sep (sep hp.ret_c (Region.contains_self _ _)) (by decide),
      hI.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_d) (by decide)]
  · apply List.ext_getElem
    · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
    · intro k h₁ h₂
      have hk : k < nb s₀ := by simpa [blocksAt] using h₁
      have := hI.blocks k hk
      simp only [hk, ite_true] at this
      simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map, List.getElem_range,
        List.getElem_zipWith, List.length_map, List.length_range]
      rw [blockAt_writeW_sep _ _ (sep hp.c_d.symm (hp.in_out hk)), this]
  · exact blockAt_store _ _ _

/-! ## The whole function -/

/-- The blocks left after `c`, eight and then one at a time, and the counter
stored: what follows `ctrLoad` here, and the sixteen-block loop of
`vg_aes_ctr32_vaes`. -/
theorem tail_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c₀ : Nat} {s₁ : State}
    (hI₁ : Inv to s₀ c₀ c₀ s₁) (hcf : s₁.cf = some (decide (nb s₀ - c₀ < 8))) :
    WP isa (ctrTail to) s₁ fun s' => gprPreserved s₀ s' ∧ Post to s₀ s' := by
  have hn := nb_lt hp
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nb s₀ - c < 8 ∧ Inv to s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nb s₀ - c₀ < 8)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c + 8 ≤ nb s₀ ∧ Inv to s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (body8 to) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, nb s₀ - c < 8 ∧ Inv to s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body8_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], nb s₀ - (c + 8), by omega_arith, c + 8, rfl, by omega_arith, hI'⟩
      exact WP.loop (M := isa) I8 hstep (nb s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_arith, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv to s₀ (nb s₀) (nb s₀)) ?_ fun s₄ hI₄ => ctrStore_ok hp hI₄)
  refine WP.ite (decide (nb s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = nb s₀ := by have := hI₃.le; simp at h; omega_arith
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c < nb s₀ ∧ Inv to s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (body1 to) s (fun s' =>
        (eval .ne s' = some false ∧ Inv to s₀ (nb s₀) (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nb s₀ - (c + 1) = 0
      · have : c + 1 = nb s₀ := by omega_arith
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], nb s₀ - (c + 1), by omega_arith, c + 1, rfl, by omega_arith, hI'⟩
    have hlt : c < nb s₀ := by have := hI₃.le; simp at h; omega_arith
    exact WP.loop (M := isa) I1 hstep (nb s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

theorem correct {to : Bool} {s₀ : State} (hp : Pre to s₀) :
    WP isa (ctr32T to) s₀ fun s' => gprPreserved s₀ s' ∧ Post to s₀ s' :=
  WP.seq (WP.mono (ctrLoad_ok hp) fun _ ⟨hI₁, hcf⟩ => tail_ok hp hI₁ (by simpa using hcf))

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000
    | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : ctr32X86_64.pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ ctr32X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem ctr32To_correct (s : State) (hs : ctr32ToX86_64.pre s) :
    ∃ t s', Exec isa ctr32To s t s' ∧ abiPreserved s s' ∧ ctr32ToX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (preTo_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem ctr32_ct : ConstantTime isa ctr32X86_64.pre ctr32X86_64.pub ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32To_ct : ConstantTime isa ctr32ToX86_64.pre ctr32ToX86_64.pub ctr32To := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r11]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Aes.X86_64.AesNi
