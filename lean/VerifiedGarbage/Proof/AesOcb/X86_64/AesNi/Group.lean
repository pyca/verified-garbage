module

public import VerifiedGarbage.Impl.AesOcb.X86_64AesNi
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Proof.Aes.InvRounds
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
-- separate module: it builds alongside `Setup`, which `Pass` also imports

/-!
# One-pass AES-OCB with AES-NI on x86-64: the blocks of a group

Untrusted: everything here is checked by Lean. `gPreList_ok`: `gPre` loads
block register `k` from `r11 + 16 (t + k)`, stores its offset
`xmm12 ⊕ C[t + k]` (`C` at `W + cO`) at `W + ofO + 16 (t + k)` and XORs it
in; for `seal` it adds the block to the checksum in `xmm10` first.
`gPostList_ok`: `gPost` adds each block register to the sum (`HASH`), or
XORs its offset in again and stores it back (and for `open` adds it to the
checksum).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.AesOcb.X86_64 (at_)
open VG.Impl.AesOcb.X86_64AesNi (Mode gPre gPost cO ofO)
open VG.Proof.Aes.X86_64.AesNi (inRegions_wr ofInt_natCast)
open VG.Proof.AesCcm.X86_64 (in_off in_left covers_left)

/-- The address `p + d`, for a byte offset `d`. -/
abbrev at' (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = at' (s.gpr b) d := by
  rw [show s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) from Proof.Aes.X86_64.AesNi.ea_at s b d,
    ofInt_natCast]

/-- The registers a group's blocks are in: none of `xmm10`, `xmm11`, `xmm12`. -/
abbrev Free (b : XReg) : Prop := b ≠ .xmm10 ∧ b ≠ .xmm11 ∧ b ≠ .xmm12

/-! ## Before AES -/

theorem gPre1_ok (md : Mode) (b : XReg) (d : Nat) (s : State) (hb : Free b)
    (hd : InRegions (s.rd ++ s.wr) (at' (s.gpr .r11) d) 16)
    (hc : InRegions (s.rd ++ s.wr) (at' (s.gpr .r15) (cO + d)) 16)
    (ho : InRegions s.wr (at' (s.gpr .r15) (ofO + d)) 16) :
    WP isa (.block (([.movdquLoad b (at_ .r11 d)] : List Instr) ++
      (if md = .seal then ([.xop (.bin .pxor .xmm10 b)] : List Instr) else []) ++
      ([.movdquLoad .xmm11 (at_ .r15 (cO + d)), .xop (.bin .pxor .xmm11 .xmm12),
        .movdquStore (at_ .r15 (ofO + d)) .xmm11, .xop (.bin .pxor b .xmm11)] : List Instr))) s
      fun s' =>
      s'.xmm b = s.mem.readW (at' (s.gpr .r11) d) 128 ^^^
        (s.mem.readW (at' (s.gpr .r15) (cO + d)) 128 ^^^ s.xmm .xmm12) ∧
      s'.xmm .xmm10 = (if md = .seal then s.xmm .xmm10 ^^^ s.mem.readW (at' (s.gpr .r11) d) 128
        else s.xmm .xmm10) ∧
      s'.mem = s.mem.writeW (at' (s.gpr .r15) (ofO + d))
        (s.mem.readW (at' (s.gpr .r15) (cO + d)) 128 ^^^ s.xmm .xmm12) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [.xmm10, .xmm11, b] → s'.xmm r = s.xmm r) := by
  obtain ⟨b10, b11, b12⟩ := hb
  apply WP.of_runBlock
  by_cases hm : md = .seal
  · simp only [hm, ↓reduceIte, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, XOp.exec, isa, State.setXmm, State.load128, State.store128_eq, ea_at, hd, hc, ho, Option.map_some,
      Option.some.injEq, exists_eq_left', b10, b11, b12, Ne.symm b10, Ne.symm b11, Ne.symm b12]
    refine ⟨by simp [XBinOp.eval, b10, b11, b12], by simp [XBinOp.eval, BitVec.xor_comm, b10, b11, b12],
      by simp [State.setMem, XBinOp.eval], rfl, rfl, rfl, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]
  · simp only [hm, ↓reduceIte, List.cons_append, List.nil_append, List.append_nil, runBlock_cons, runStep_some,
      runBlock_nil, exec, XOp.exec, isa, State.setXmm, State.load128, State.store128_eq, ea_at, hd, hc, ho,
      Option.map_some, Option.some.injEq, exists_eq_left', b10, b11, b12, Ne.symm b10, Ne.symm b11,
      Ne.symm b12]
    refine ⟨by simp [XBinOp.eval, b10, b11, b12], by simp [b10, b11, b12, Ne.symm b10], by simp [State.setMem, XBinOp.eval],
      rfl, rfl, rfl, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

/-- `f 0 ⊕ … ⊕ f (n − 1)`. -/
def xorN (f : Nat → BitVec 128) : Nat → BitVec 128
  | 0 => 0
  | n + 1 => xorN f n ^^^ f n

theorem xorN_cons (f : Nat → BitVec 128) (n : Nat) : xorN f (n + 1) = f 0 ^^^ xorN (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [xorN]
  | succ n ih => rw [xorN, ih, xorN, BitVec.xor_assoc]

theorem xorN_congr {f g : Nat → BitVec 128} {n : Nat} (h : ∀ k < n, f k = g k) : xorN f n = xorN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorN, xorN, ih (fun k hk => h k (by omega_arith)), h n (by omega_arith)]

/-- `gPre` on the blocks `t`, … of a group. -/
theorem gPreList_ok (md : Mode) (rs : List XReg) (t : Nat) (s : State) {B W : Addr} {wn : Nat}
    (hnd : rs.Nodup) (hf : ∀ b ∈ rs, Free b) (h11 : s.gpr .r11 = B) (h15 : s.gpr .r15 = W)
    (hl : t + rs.length ≤ 8) (hwn : ofO + 128 ≤ wn) (hw : wn < 2 ^ 64)
    (hD : Covers [⟨B, 16 * (t + rs.length)⟩] (s.rd ++ s.wr)) (hW : Covers [⟨W, wn⟩] s.wr)
    (hDW : Region.Disjoint ⟨B, 16 * (t + rs.length)⟩ ⟨W, wn⟩) :
    WP isa (.block (gPre md rs t)) s fun s' =>
      (∀ k (h : k < rs.length), s'.xmm rs[k] = s.mem.readW (at' B (16 * (t + k))) 128 ^^^
          (s.mem.readW (at' W (cO + 16 * (t + k))) 128 ^^^ s.xmm .xmm12)) ∧
      s'.xmm .xmm10 = (if md = .seal then
          s.xmm .xmm10 ^^^ xorN (fun k => s.mem.readW (at' B (16 * (t + k))) 128) rs.length
        else s.xmm .xmm10) ∧
      (∀ k < rs.length, s'.mem.readW (at' W (ofO + 16 * (t + k))) 128 =
        s.mem.readW (at' W (cO + 16 * (t + k))) 128 ^^^ s.xmm .xmm12) ∧
      Frame [⟨at' W (ofO + 16 * t), 16 * rs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ .xmm10 :: .xmm11 :: rs → s'.xmm r = s.xmm r) := by
  have cof : cO + 128 ≤ ofO := by decide
  induction rs generalizing t s with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h (by simp), by split <;> simp [xorN], fun _ h => absurd h (by simp),
      Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hl hD hDW
    obtain ⟨hb, hbs⟩ := List.nodup_cons.mp hnd
    have fb := hf b List.mem_cons_self
    have fbs : ∀ c ∈ bs, Free c := fun c hc => hf c (List.mem_cons_of_mem _ hc)
    rw [gPre, WP.block_append_iff]
    have hbl' : 16 * (t + (bs.length + 1)) < 2 ^ 64 := by omega_arith
    have hd0 : InRegions (s.rd ++ s.wr) (at' (s.gpr .r11) (16 * t)) 16 := by
      rw [h11]; exact in_off hD (by omega_arith) hbl'
    have hc0 : InRegions (s.rd ++ s.wr) (at' (s.gpr .r15) (cO + 16 * t)) 16 := by
      rw [h15]; exact in_left (in_off hW (by omega_arith) hw)
    have ho0 : InRegions s.wr (at' (s.gpr .r15) (ofO + 16 * t)) 16 := by
      rw [h15]; exact in_off hW (by omega_arith) hw
    refine WP.mono (gPre1_ok md b (16 * t) s fb hd0 hc0 ho0) fun s₁ ⟨v₁, x₁, m₁, g₁, rd₁, wr₁, o₁⟩ => ?_
    simp only [h11, h15] at v₁ x₁ m₁
    -- What the first block's offset store leaves.
    have dSep : ∀ k < bs.length, s₁.mem.readW (at' B (16 * (t + 1 + k))) 128 =
        s.mem.readW (at' B (16 * (t + 1 + k))) 128 := fun k hk => by
      rw [m₁]
      exact Mem.readW_writeW_sep (hDW.sep (Offset.contains_base B (by omega_arith) (by omega_arith))
        (Offset.contains_base W (by omega_arith) (by omega_arith))) (by decide)
    have cSep : ∀ k < bs.length, s₁.mem.readW (at' W (cO + 16 * (t + 1 + k))) 128 =
        s.mem.readW (at' W (cO + 16 * (t + 1 + k))) 128 := fun k hk => by
      rw [m₁]
      exact Mem.readW_writeW_sep (Offset.sep W (.inl (by omega_arith)) (by omega_arith)
        (by omega_arith)) (by decide)
    have x12 : s₁.xmm .xmm12 = s.xmm .xmm12 := o₁ _ (by simp [Ne.symm fb.2.2])
    refine WP.mono (ih (t + 1) s₁ hbs fbs (by rw [g₁, h11]) (by rw [g₁, h15]) (by omega_arith)
        (by rw [rd₁, wr₁, show t + 1 + bs.length = t + (bs.length + 1) by omega_arith]; exact hD)
        (by rw [wr₁]; exact hW) (by rw [show t + 1 + bs.length = t + (bs.length + 1) by omega_arith]; exact hDW))
      fun s' ⟨v, x10, mo, fr, g, rd, wr, o⟩ => ?_
    have sb : s'.xmm b = s₁.xmm b := o b (by simp [hb, fb.1, fb.2.1])
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero => simp only [List.getElem_cons_zero, Nat.add_zero]; rw [sb, v₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [v k hk', dSep k hk', cSep k hk', x12, show t + 1 + k = t + (k + 1) by omega_arith]
    · rw [x10, x₁]
      by_cases hm : md = .seal
      · simp only [hm, ↓reduceIte, List.length_cons]
        rw [xorN_cons, ← BitVec.xor_assoc, xorN_congr (fun k hk => dSep k hk)]
        simp only [Nat.add_zero, show ∀ k, t + 1 + k = t + (k + 1) from fun k => by omega_arith]
      · simp only [hm, ↓reduceIte]
    · cases k with
      | zero =>
        rw [Nat.add_zero]
        rw [fr.readW (r := ⟨at' W (ofO + 16 * t), 16⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith)
            (by omega_arith)) (by decide)]
        rw [m₁, Mem.readW_writeW_self _ _ 16 _ (by decide)]
      | succ k =>
        have hk' : k < bs.length := by simpa using hk
        rw [show t + (k + 1) = t + 1 + k by omega_arith, mo k hk', cSep k hk', x12]
    · simp only [List.length_cons]
      refine Frame.trans (Frame.sub (rs := [⟨at' W (ofO + 16 * t), 16⟩]) ?_ fun r hr => ?_)
        (Frame.sub fr fun r hr => ?_)
      · rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub W (by omega_arith) (by omega_arith)⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub W (by omega_arith) (by omega_arith)⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [o r (by simp [hr.1, hr.2.1, hr.2.2.2]), o₁ r (by simp [hr.1, hr.2.1, hr.2.2.1])]

/-! ## After AES -/

/-- What `gPost` makes of block register `b` and its offset `o`: the block
stored (`seal`, `open`), and what is added to `xmm10`. -/
def postOut (b o : BitVec 128) : BitVec 128 := b ^^^ o

theorem gPost1_ok (md : Mode) (b : XReg) (d : Nat) (s : State) (hb : Free b)
    (hd : md ≠ .hash → InRegions s.wr (at' (s.gpr .r11) d) 16)
    (ho : InRegions (s.rd ++ s.wr) (at' (s.gpr .r15) (ofO + d)) 16) :
    WP isa (.block ((if md = .hash then [.xop (.bin .pxor .xmm10 b)] else
      ([.movdquLoad .xmm11 (at_ .r15 (ofO + d)), .xop (.bin .pxor b .xmm11),
        .movdquStore (at_ .r11 d) b] : List Instr) ++
      (if md = .open then [.xop (.bin .pxor .xmm10 b)] else [])))) s
      fun s' =>
      s'.xmm .xmm10 = (if md = .hash then s.xmm .xmm10 ^^^ s.xmm b
        else if md = .open then s.xmm .xmm10 ^^^ (s.xmm b ^^^ s.mem.readW (at' (s.gpr .r15) (ofO + d)) 128)
        else s.xmm .xmm10) ∧
      s'.mem = (if md = .hash then s.mem else
        s.mem.writeW (at' (s.gpr .r11) d) (s.xmm b ^^^ s.mem.readW (at' (s.gpr .r15) (ofO + d)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ [.xmm10, .xmm11, b] → s'.xmm r = s.xmm r) := by
  obtain ⟨b10, b11, b12⟩ := hb
  apply WP.of_runBlock
  rcases md with _ | _ | _
  · simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp [XBinOp.eval], trivial, trivial, trivial, trivial, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1]
  · have hd := hd (by decide)
    have hd' := inRegions_wr hd
    simp only [reduceCtorEq, ↓reduceIte, List.append_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
      XOp.exec, isa, State.setXmm, State.load128, State.store128_eq, ea_at, hd, hd', ho, Option.map_some,
      Option.some.injEq, exists_eq_left', b11, Ne.symm b11]
    refine ⟨by simp [Ne.symm b10], by simp [State.setMem, XBinOp.eval], rfl, rfl, rfl, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.1, hr.2.2]
  · have hd := hd (by decide)
    have hd' := inRegions_wr hd
    simp only [reduceCtorEq, ↓reduceIte, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, XOp.exec, isa, State.setXmm, State.load128, State.store128_eq, ea_at, hd, hd', ho,
      Option.map_some, Option.some.injEq, exists_eq_left', b11, Ne.symm b11]
    refine ⟨by simp [XBinOp.eval, b10, Ne.symm b10], by simp [State.setMem, XBinOp.eval, b10, Ne.symm b10],
      rfl, rfl, rfl, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

/-- Block register `k` of `rs`. -/
abbrev reg (rs : List XReg) (k : Nat) : XReg := rs.getD k .xmm0

/-- `gPost` on the blocks `t`, … of a group: `Y k`, block register `k` XORed
with its offset from the buffer, is stored back (`seal`, `open`) and added
to the checksum (`open`); `HASH` adds the block registers to the sum. -/
theorem gPostList_ok (md : Mode) (rs : List XReg) (t : Nat) (s : State) {B W : Addr} {wn : Nat}
    (hnd : rs.Nodup) (hf : ∀ b ∈ rs, Free b) (h11 : s.gpr .r11 = B) (h15 : s.gpr .r15 = W)
    (hl : t + rs.length ≤ 8) (hwn : ofO + 128 ≤ wn) (hw : wn < 2 ^ 64)
    (hD : md ≠ .hash → Covers [⟨B, 16 * (t + rs.length)⟩] s.wr) (hW : Covers [⟨W, wn⟩] (s.rd ++ s.wr))
    (hDW : Region.Disjoint ⟨B, 16 * (t + rs.length)⟩ ⟨W, wn⟩) :
    WP isa (.block (gPost md rs t)) s fun s' =>
      s'.xmm .xmm10 = (if md = .hash then s.xmm .xmm10 ^^^ xorN (fun k => s.xmm (reg rs k)) rs.length
        else if md = .open then s.xmm .xmm10 ^^^ xorN (fun k => s.xmm (reg rs k) ^^^
          s.mem.readW (at' W (ofO + 16 * (t + k))) 128) rs.length
        else s.xmm .xmm10) ∧
      (md = .hash → s'.mem = s.mem) ∧
      (md ≠ .hash → ∀ k < rs.length, s'.mem.readW (at' B (16 * (t + k))) 128 =
        s.xmm (reg rs k) ^^^ s.mem.readW (at' W (ofO + 16 * (t + k))) 128) ∧
      Frame [⟨at' B (16 * t), 16 * rs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ .xmm10 :: .xmm11 :: rs → s'.xmm r = s.xmm r) := by
  induction rs generalizing t s with
  | nil =>
    refine WP.block_nil ⟨?_, fun _ => rfl, fun _ _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    split
    · simp [xorN]
    · split <;> simp [xorN]
  | cons b bs ih =>
    simp only [List.length_cons] at hl hD hDW
    obtain ⟨hb, hbs⟩ := List.nodup_cons.mp hnd
    have fb := hf b List.mem_cons_self
    have fbs : ∀ c ∈ bs, Free c := fun c hc => hf c (List.mem_cons_of_mem _ hc)
    rw [gPost, WP.block_append_iff]
    have h16 : 16 * (t + (bs.length + 1)) < 2 ^ 64 := by omega_arith
    have hd0 : md ≠ .hash → InRegions s.wr (at' (s.gpr .r11) (16 * t)) 16 := fun hm => by
      rw [h11]; exact in_off (hD hm) (by omega_arith) h16
    have ho0 : InRegions (s.rd ++ s.wr) (at' (s.gpr .r15) (ofO + 16 * t)) 16 := by
      rw [h15]; exact in_off hW (by omega_arith) hw
    refine WP.mono (gPost1_ok md b (16 * t) s fb hd0 ho0) fun s₁ ⟨x₁, m₁, g₁, rd₁, wr₁, o₁⟩ => ?_
    simp only [h11, h15] at x₁ m₁
    -- What the first block's store leaves.
    have oSep : ∀ k < bs.length, s₁.mem.readW (at' W (ofO + 16 * (t + 1 + k))) 128 =
        s.mem.readW (at' W (ofO + 16 * (t + 1 + k))) 128 := fun k hk => by
      rw [m₁]
      split
      · rfl
      · exact Mem.readW_writeW_sep (hDW.symm.sep (Offset.contains_base W (by omega_arith) (by omega_arith))
          (Offset.contains_base B (by omega_arith) (by omega_arith))) (by decide)
    have xs : ∀ k < bs.length, s₁.xmm (reg bs k) = s.xmm (reg (b :: bs) (k + 1)) := fun k hk => by
      simp only [reg, List.getD_cons_succ]
      have hm : bs.getD k .xmm0 ∈ bs :=
        List.mem_iff_getElem.mpr ⟨k, hk, by simp [List.getD_eq_getElem?_getD, hk]⟩
      exact o₁ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(fbs _ hm).1, (fbs _ hm).2.1, fun h => hb (h ▸ hm)⟩)
    refine WP.mono (ih (t + 1) s₁ hbs fbs (by rw [g₁, h11]) (by rw [g₁, h15]) (by omega_arith)
        (fun hm => by rw [wr₁, show t + 1 + bs.length = t + (bs.length + 1) by omega_arith]; exact hD hm)
        (by rw [rd₁, wr₁]; exact hW)
        (by rw [show t + 1 + bs.length = t + (bs.length + 1) by omega_arith]; exact hDW))
      fun s' ⟨x10, mh, mo, fr, g, rd, wr, o⟩ => ?_
    refine ⟨?_, fun hm => ?_, fun hm k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · rw [x10, x₁]
      rcases md with _ | _ | _
      · simp only [↓reduceIte, List.length_cons]
        rw [xorN_cons, ← BitVec.xor_assoc, xorN_congr (fun k hk => xs k hk)]
        rfl
      · simp only [reduceCtorEq, ↓reduceIte]
      · simp only [reduceCtorEq, ↓reduceIte, List.length_cons]
        rw [xorN_cons, ← BitVec.xor_assoc, xorN_congr (fun k hk => by rw [xs k hk, oSep k hk])]
        simp only [reg, List.getD_cons_zero, Nat.add_zero, BitVec.xor_assoc,
          show ∀ k, t + 1 + k = t + (k + 1) from fun k => by omega_arith]
    · rw [mh hm, m₁]; simp [hm]
    · simp only [m₁, hm, ↓reduceIte] at mo fr oSep ⊢
      cases k with
      | zero =>
        rw [Nat.add_zero]
        rw [fr.readW (r := ⟨at' B (16 * t), 16⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint B (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
          Mem.readW_writeW_self _ _ 16 _ (by decide)]
        rfl
      | succ k =>
        have hk' : k < bs.length := by simpa using hk
        rw [show t + (k + 1) = t + 1 + k by omega_arith, mo hm k hk', xs k hk', oSep k hk']
    · simp only [List.length_cons]
      refine Frame.trans (Frame.sub (rs := [⟨at' B (16 * t), 16⟩]) ?_ fun r hr => ?_)
        (Frame.sub fr fun r hr => ?_)
      · rw [m₁]; split
        · exact Frame.refl _ _
        · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub B (by omega_arith) (by omega_arith)⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub B (by omega_arith) (by omega_arith)⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [o r (by simp [hr.1, hr.2.1, hr.2.2.2]), o₁ r (by simp [hr.1, hr.2.1, hr.2.2.1])]

/-! ## A group -/

open VG.Impl.Aes.X86_64.AesNi (regs8)
open VG.Impl.AesOcb.X86_64AesNi (group imcPtr imcO cipher)
open VG.Proof.Aes.X86_64.AesNi (Keys DKeys XFrame st aes_ok aesDec_ok)

/-- The block registers of a group of `r`. -/
abbrev regsOf (r : Nat) : List XReg := regs8.take r

theorem regsOf_nodup (r : Nat) : (regsOf r).Nodup := (List.take_sublist r regs8).nodup (by decide)

theorem regs8_free : ∀ b ∈ regs8, Free b := by decide

theorem regsOf_free (r : Nat) : ∀ b ∈ regsOf r, Free b := fun b hb => regs8_free b (List.mem_of_mem_take hb)

theorem regsOf_8 (r : Nat) : .xmm8 ∉ regsOf r := fun h => absurd (List.mem_of_mem_take h) (by decide)

theorem regsOf_length {r : Nat} (hr : r ≤ 8) : (regsOf r).length = r := by
  simp only [regsOf, List.length_take, show regs8.length = 8 from rfl]; omega_arith

/-- The key schedule, after code that keeps `rdi` and the permissions and
writes only memory apart from it. -/
theorem keys_of_frame {nr : Nat} {w : List Byte} {s s' : State} (hK : Keys nr w s)
    (hdi : s'.gpr .rdi = s.gpr .rdi) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, Region.Disjoint ⟨s.gpr .rdi, 240⟩ r) : Keys nr w s' := by
  have hle := hK.le
  refine ⟨?_, hle, by rw [hrd, hwr, hdi]; exact hK.keys⟩
  rw [hdi, Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega_arith)))
    (by omega_arith)]
  exact hK.sched

/-- The last two instructions of a group: the offset of its last block to
`xmm12`, and `r11` past the group. -/
theorem groupEnd_ok (r : Nat) (s : State) {W : Addr}
    (h15 : s.gpr .r15 = W) (ho : InRegions (s.rd ++ s.wr) (at' W (ofO + 16 * (r - 1))) 16) :
    WP isa (.block ([.movdquLoad .xmm12 (at_ .r15 (ofO + 16 * (r - 1))), Impl.AesOcb.X86_64.addi .r11 (16 * r)] :
      List Instr)) s fun s' =>
      s'.xmm .xmm12 = s.mem.readW (at' W (ofO + 16 * (r - 1))) 128 ∧
      s'.gpr .r11 = s.gpr .r11 + (BitVec.ofNat 32 (16 * r)).signExtend 64 ∧
      (∀ x, x ≠ .r11 → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm12 → s'.xmm x = s.xmm x) := by
  apply WP.of_runBlock
  rw [← h15] at ho
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.setXmm, State.load128, ea_at, ho,
    Option.map_some, Impl.AesOcb.X86_64.addi, execAlu, readSrc, Option.bind_some, Option.some.injEq,
    exists_eq_left', ↓reduceIte]
  refine ⟨by simp [RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, h15], by simp [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags],
    fun x hx => by simp [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hx], by simp [RegUpd.mem_setReg,
    RegUpd.mem_arithFlags], by simp [RegUpd.rd_setReg, RegUpd.rd_arithFlags],
    by simp [RegUpd.wr_setReg, RegUpd.wr_arithFlags],
    fun x hx => by simp [RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, hx]⟩

/-- The round keys `1 … nr − 1` through `aesimc`, at `W + imcO + 16 j`, as
`open`'s inverse cipher reads them. -/
def ImcAt (nr : Nat) (w : List Byte) (W : Addr) (m : Mem) : Prop :=
  ∀ j, 1 ≤ j → j < nr →
    st (m.readW (at' W (imcO + 16 * j)) 128) = Spec.Aes.invMixColumns (Proof.Aes.rkState (Spec.Aes.roundKey w j))

/-- `imcPtr`: `r8 ← W + imcO`. -/
theorem imcPtr_ok (s : State) {W : Addr} (h15 : s.gpr .r15 = W) :
    WP isa (.block imcPtr) s fun s' => s'.gpr .r8 = at' W imcO ∧ (∀ x, x ≠ .r8 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  refine ⟨_, by orun [imcPtr, h15], ?_⟩
  refine ⟨by simp [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, imcO, at', h15], fun x hx => by
    simp [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hx], rfl, rfl, rfl, rfl⟩

theorem reg_mem {rs : List XReg} {k : Nat} (hk : k < rs.length) : reg rs k ∈ rs :=
  List.mem_iff_getElem.mpr ⟨k, hk, by simp [reg, List.getD_eq_getElem?_getD, hk]⟩

theorem reg_eq {rs : List XReg} {k : Nat} (hk : k < rs.length) : reg rs k = rs[k] := by
  simp [reg, List.getD_eq_getElem?_getD, hk]

/-- A group of `r` blocks (`1 ≤ r ≤ 8`) at `B`, with the offset in `xmm12`
and `C` at `W + cO`: block `k` is `P k = B + 16 k`, its offset `O k` is
`C[k] ⊕ xmm12`, and `Y k` is AES of `P k ⊕ O k` (`invCipher` for `open`). -/
theorem group_ok (md : Mode) (r : Nat) (hr1 : 1 ≤ r) (hr8 : r ≤ 8) (s : State) {B W : Addr} {wn nr : Nat}
    {w : List Byte} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (hK : Keys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr))
    (hI : md = .open → ImcAt nr w W s.mem) (h11 : s.gpr .r11 = B) (h15 : s.gpr .r15 = W)
    (hwn : ofO + 128 ≤ wn) (hwo : md = .open → imcO + 224 ≤ wn) (hw : wn < 2 ^ 64)
    (hD : Covers [⟨B, 16 * r⟩] (s.rd ++ s.wr)) (hDw : md ≠ .hash → Covers [⟨B, 16 * r⟩] s.wr)
    (hW : Covers [⟨W, wn⟩] s.wr) (hDW : Region.Disjoint ⟨B, 16 * r⟩ ⟨W, wn⟩)
    (hKW : Region.Disjoint ⟨s.gpr .rdi, 240⟩ ⟨W, wn⟩)
    (hKD : md ≠ .hash → Region.Disjoint ⟨s.gpr .rdi, 240⟩ ⟨B, 16 * r⟩) :
    WP isa (group md r) s fun s' => ∃ Y : Nat → BitVec 128,
      (∀ k < r, st (Y k) = (if md = .open then Spec.Aes.invCipher nr w else Spec.Aes.cipher nr w)
        (st (s.mem.readW (at' B (16 * k)) 128 ^^^ (s.mem.readW (at' W (cO + 16 * k)) 128 ^^^ s.xmm .xmm12)))) ∧
      (md ≠ .hash → ∀ k < r, s'.mem.readW (at' B (16 * k)) 128 =
        Y k ^^^ (s.mem.readW (at' W (cO + 16 * k)) 128 ^^^ s.xmm .xmm12)) ∧
      s'.xmm .xmm10 = (if md = .hash then s.xmm .xmm10 ^^^ xorN Y r
        else if md = .open then s.xmm .xmm10 ^^^ xorN (fun k => Y k ^^^
          (s.mem.readW (at' W (cO + 16 * k)) 128 ^^^ s.xmm .xmm12)) r
        else s.xmm .xmm10 ^^^ xorN (fun k => s.mem.readW (at' B (16 * k)) 128) r) ∧
      s'.xmm .xmm12 = s.mem.readW (at' W (cO + 16 * (r - 1))) 128 ^^^ s.xmm .xmm12 ∧
      s'.gpr .r11 = B + (BitVec.ofNat 32 (16 * r)).signExtend 64 ∧
      (∀ x, x ≠ .r11 → x ≠ .r8 → s'.gpr x = s.gpr x) ∧
      Frame [⟨at' W ofO, 128⟩, ⟨B, 16 * r⟩] s.mem s'.mem ∧
      (md = .hash → Frame [⟨at' W ofO, 128⟩] s.mem s'.mem) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ∉ regs8 → x ≠ .xmm8 → x ≠ .xmm10 → x ≠ .xmm11 → x ≠ .xmm12 → s'.xmm x = s.xmm x) := by
  have hl := regsOf_length hr8
  have hnd := regsOf_nodup r
  have hf := regsOf_free r
  have h8 := regsOf_8 r
  have hle := hK.le
  have cof : cO + 128 ≤ ofO := by decide
  have ofi : ofO + 128 ≤ imcO + 16 := by decide
  unfold group
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (gPreList_ok md (regsOf r) 0 s (B := B) (W := W) (wn := wn) hnd hf h11 h15 (by omega_arith) hwn hw
    (by rw [hl, Nat.zero_add]; exact hD) hW (by rw [hl, Nat.zero_add]; exact hDW))
    fun s₁ ⟨v₁, x₁, mo₁, fr₁, g₁, rd₁, wr₁, o₁⟩ => ?_
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero, hl] at v₁ x₁ mo₁ fr₁
  -- `imcPtr`, for `open`.
  have step2 : WP isa (.block (if md = .open then imcPtr else [])) s₁ fun s₁' =>
      (md = .open → s₁'.gpr .r8 = at' W imcO) ∧ (∀ x, x ≠ .r8 → s₁'.gpr x = s₁.gpr x) ∧
      s₁'.mem = s₁.mem ∧ s₁'.rd = s₁.rd ∧ s₁'.wr = s₁.wr ∧ s₁'.xmm = s₁.xmm := by
    by_cases hmo : md = .open
    · simp only [hmo, ↓reduceIte]
      exact WP.mono (imcPtr_ok s₁ (by rw [g₁, h15])) fun t ⟨a, b, c, d, e, f⟩ => ⟨fun _ => a, b, c, d, e, f⟩
    · simp only [hmo, ↓reduceIte]
      exact WP.block_nil ⟨fun h => h.elim, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono step2 fun s₁' ⟨r8₁, g₁', m₁', rd₁', wr₁', x₁'⟩ => ?_
  have gg : ∀ x, x ≠ .r8 → s₁'.gpr x = s.gpr x := fun x hx => by rw [g₁' x hx, g₁]
  have fr₁' : Frame [⟨at' W ofO, 16 * r⟩] s.mem s₁'.mem := by rw [m₁']; exact fr₁
  have keys₁ : Keys nr w s₁' := keys_of_frame hK (gg _ (by decide)) (rd₁'.trans rd₁) (wr₁'.trans wr₁) fr₁'
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hKW.sub_right (Offset.sub_base W (by omega_arith)))
  -- The cipher.
  have step3 : WP isa (cipher md (regsOf r)) s₁' fun s₂ =>
      (∀ b ∈ regsOf r, st (s₂.xmm b) =
        (if md = .open then Spec.Aes.invCipher nr w else Spec.Aes.cipher nr w) (st (s₁'.xmm b))) ∧
      XFrame (.xmm8 :: regsOf r) s₁' s₂ := by
    unfold cipher
    by_cases hmo : md = .open
    · simp only [hmo, ↓reduceIte]
      have hwo' := hwo hmo
      refine aesDec_ok (regsOf r) hnd h8 hnr s₁' ⟨keys₁, fun j h1 h2 => ⟨?_, ?_⟩⟩ (by rw [gg _ (by decide), hrsi])
        (by rw [gg _ (by decide), gg _ (by decide), hr10])
      · rw [r8₁ hmo, ofInt_natCast, rd₁', wr₁', rd₁, wr₁, Offset.add_add]
        exact in_left (in_off hW (by omega_arith) hw)
      · rw [r8₁ hmo, ofInt_natCast, Offset.add_add, m₁']
        rw [fr₁.readW (r := ⟨at' W (imcO + 16 * j), 16⟩) (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
        exact hI hmo j h1 h2
    · simp only [hmo, ↓reduceIte]
      exact aes_ok (regsOf r) hnd h8 hnr s₁' keys₁ (by rw [gg _ (by decide), hrsi])
        (by rw [gg _ (by decide), gg _ (by decide), hr10])
  refine WP.seq (WP.mono step3 fun s₂ ⟨c₂, f₂⟩ => ?_)
  have nr10 : XReg.xmm10 ∉ regsOf r := fun h => (hf _ h).1 rfl
  have g₂ : ∀ x, x ≠ .r8 → s₂.gpr x = s.gpr x := fun x hx => by rw [f₂.gpr, gg x hx]
  have m₂ : s₂.mem = s₁.mem := by rw [f₂.mem, m₁']
  have rd₂ : s₂.rd = s.rd := by rw [f₂.rd, rd₁', rd₁]
  have wr₂ : s₂.wr = s.wr := by rw [f₂.wr, wr₁', wr₁]
  have x10₂ : s₂.xmm .xmm10 = s₁.xmm .xmm10 := by
    rw [f₂.xmm _ (by simp [nr10]), x₁']
  rw [WP.block_append_iff]
  refine WP.mono (gPostList_ok md (regsOf r) 0 s₂ (B := B) (W := W) (wn := wn) hnd hf (by rw [g₂ _ (by decide), h11])
      (by rw [g₂ _ (by decide), h15]) (by omega_arith) hwn hw
      (fun hm => by rw [wr₂, hl, Nat.zero_add]; exact hDw hm) (by rw [rd₂, wr₂]; exact covers_left hW)
      (by rw [hl, Nat.zero_add]; exact hDW))
    fun s₃ ⟨x10₃, mh₃, mo₃, fr₃, g₃, rd₃, wr₃, o₃⟩ => ?_
  simp only [Nat.zero_add, Nat.mul_zero, hl] at x10₃ mo₃ fr₃
  have m₃W : ∀ d, d + 16 ≤ wn → s₃.mem.readW (at' W d) 128 = s₂.mem.readW (at' W d) 128 := fun d hd =>
    fr₃.readW (r := ⟨at' W d, 16⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact (hDW.symm.sub_left (Offset.sub_base W hd)).sub_right (Offset.sub_base B (by omega_arith)))
      (by decide)
  refine WP.mono (groupEnd_ok r s₃ (W := W) (by rw [g₃, g₂ _ (by decide), h15])
      (by rw [rd₃, wr₃, rd₂, wr₂]; exact in_left (in_off hW (by omega_arith) hw)))
    fun s' ⟨x12, r11', g', m', rd', wr', o'⟩ => ?_
  refine ⟨fun k => s₂.xmm (reg (regsOf r) k), fun k hk => ?_, fun hm k hk => ?_, ?_, ?_, ?_,
    fun x h1 h2 => ?_, ?_, fun hm => ?_, rd'.trans (rd₃.trans rd₂), wr'.trans (wr₃.trans wr₂),
    fun x h1 h2 h3 h4 h5 => ?_⟩
  · have hk' : k < (regsOf r).length := by rw [hl]; exact hk
    rw [c₂ _ (reg_mem hk'), x₁', reg_eq hk', v₁ k hk]
  · rw [m', mo₃ hm k hk, m₂, mo₁ k hk]
  · rw [o' .xmm10 (by decide), x10₃, x10₂, x₁]
    rcases md with _ | _ | _
    · simp only [↓reduceIte, reduceCtorEq, hl]
    · simp only [↓reduceIte, reduceCtorEq]
    · simp only [↓reduceIte, reduceCtorEq, hl]
      rw [xorN_congr fun k hk => by rw [m₂, mo₁ k hk]]
  · rw [x12, m₃W _ (by omega_arith), m₂, mo₁ (r - 1) (by omega_arith)]
  · rw [r11', g₃, g₂ _ (by decide), h11]
  · rw [g' x h1, g₃, g₂ x h2]
  · refine Frame.trans (Frame.sub fr₁' fun r' hr' => ?_) ?_
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega_arith)⟩
    · rw [m', ← f₂.mem]
      refine Frame.sub fr₃ fun r' hr' => ?_
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base B (by omega_arith)⟩
  · rw [m', mh₃ hm, f₂.mem]
    exact Frame.sub fr₁' fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
  · have nx : x ∉ regsOf r := fun h => h1 (List.mem_of_mem_take h)
    rw [o' x h5, o₃ x (by simp [h4, h3, nx]), f₂.xmm x (by simp [h2, nx]), x₁', o₁ x (by simp [h4, h3, nx])]

end VG.Proof.AesOcb.X86_64.AesNi
