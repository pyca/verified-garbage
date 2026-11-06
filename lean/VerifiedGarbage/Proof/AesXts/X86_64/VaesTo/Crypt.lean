module

public import VerifiedGarbage.Proof.AesXts.X86_64.To.Contract
public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Loop
public import VerifiedGarbage.Impl.AesXts.X86_64VaesTo
public import VerifiedGarbage.Proof.AesXts.X86_64.Steps
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Tail
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Enc
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Dec
public import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Loop
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.PrePost
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.TailOps
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Call
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Setup
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Top
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Step

/-!
# One-pass XTS-AES on x86-64, out of place: correctness

`encryptVaes_wp`, `decryptVaes_wp`, `encryptAesNi_wp` and
`decryptAesNi_wp`: the out-of-place one-pass functions meet
`To.xtsToX86_64`. The proofs are those of the in-place functions
(`Proof/AesXts/X86_64/Vaes/` and `AesNi/`), section by section below: the
arguments and the loads from `src`, the eight-block loops, the setup, the
blocks left, the whole function, and what the rounds need.
-/

@[expose] public section

/-! ## One-pass XTS-AES on x86-64, out of place: the arguments, and the blocks loaded from `src`

The out-of-place one-pass functions (`Impl/AesXts/X86_64VaesTo.lean`), with
the arguments of `To.xtsToX86_64` (`schedule = rdi`, `rounds = rsi`,
`tweak = rdx`, `src = rcx`, `n = r8`, `scratch = r9`, `dst = r10`). The proofs
are those of the in-place functions (`Proof/AesXts/X86_64/Vaes/`), with the
data their invariants follow being `dst` (`Dp`, `dataR`, `blk`), where
`r11` walks: only the loads differ, from `[r11 + rcx + d]` with
`rcx = src - dst` (`ix`, `ea_ix`), the blocks at `src` (`sblk`), which
nothing writes (`UPre.src_kept`). `pre1To_ok`, `preListTo_ok`,
`tPre1To_ok` and `tPreListTo_ok` are `Vaes.pre1_ok`, `Vaes.preList_ok`,
`Vaes.tPre1_ok` and `Vaes.tPreList_ok` with those loads.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.AesXts.X86_64VaesTo (ix preXor tPre)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr ofInt_natCast)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi)
open VG.Proof.AesXts.X86_64.Vaes (addr2)

export VG.Proof.AesCbc.X86_64 (W R Iv N S schR ivR scrR wK iv0)

section
variable (s₀ : State)

abbrev Sr : Addr := s₀.gpr .rcx
/-- `dst`. -/
abbrev Dp : Addr := s₀.gpr .r10

abbrev srcR : Region := ⟨Sr s₀, 16 * N s₀⟩
abbrev dataR : Region := ⟨Dp s₀, 16 * N s₀⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16

/-- Block `k` of `dst`. -/
abbrev blk (k : Nat) : Addr := Dp s₀ + BitVec.ofNat 64 (16 * k)
/-- Block `k` of `src`. -/
abbrev sblk (k : Nat) : Addr := Sr s₀ + BitVec.ofNat 64 (16 * k)
/-- `src - dst`. -/
abbrev Dl : Addr := Sr s₀ - Dp s₀

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, srcR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  src_iv : (srcR s₀).Disjoint (ivR s₀)
  src_data : (srcR s₀).Disjoint (dataR s₀)
  src_scr : (srcR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  ret_iv : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (ivR s₀)
  ret_data : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (dataR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (scrR s₀)
  stk_sch : (stkR s₀).Disjoint (schR s₀)
  stk_src : (stkR s₀).Disjoint (srcR s₀)
  stk_iv : (stkR s₀).Disjoint (ivR s₀)
  stk_data : (stkR s₀).Disjoint (dataR s₀)
  stk_scr : (stkR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  src_wrap : (Sr s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rsp_lo : 16 ≤ (s₀.gpr .rsp).toNat
  rsp_hi : (s₀.gpr .rsp).toNat + 8 ≤ 2 ^ 64
  n_lt : N s₀ < 2 ^ 59
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (To.xtsToX86_64 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.src_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨sblk s₀ k, 16⟩ (srcR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.blk_toNat (hp : UPre s₀) {k : Nat} (hk : k < N s₀) : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_wrap
  rw [blk, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem cIv0 : (ivR s₀).Contains (Iv s₀) 8 := by
  simp only [Region.Contains, BitVec.sub_self]; simp

theorem cIv8 : (ivR s₀).Contains (Iv s₀ + BitVec.ofNat 64 8) 8 :=
  Offset.contains_base _ (by decide) (by decide)

/-- The tweak of block `b + j` is at `slot s₀ j`. -/
theorem slot_scr {j : Nat} (hj : j < 16) : Region.Sub ⟨Vaes.slot s₀ j, 16⟩ (scrR s₀) :=
  UPre.scr_sub (by simp only [Impl.AesXts.X86_64Vaes.bufOff]; omega)

theorem buf_scr : Region.Sub (Vaes.bufR s₀) (scrR s₀) := UPre.scr_sub (d := Impl.AesXts.X86_64Vaes.bufOff)
  (n := 1920) (by decide)

/-- `n` blocks from block `c` lie in `dst`. -/
theorem group_data_n {c n : Nat} (hc : c + n ≤ N s₀) : Region.Sub ⟨blk s₀ c, 16 * n⟩ (dataR s₀) := by
  rw [blk]; exact Offset.sub_base _ (by omega)

/-- Block `c + 2k + l` from block `c`. -/
theorem blk_lane (c k l : Nat) : blk s₀ c + BitVec.ofNat 64 (32 * (0 + k) + 16 * l) = blk s₀ (c + (2 * k + l)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

/-- The same block of `src` and of `dst`, `src - dst` apart. -/
theorem sblk_eq (k : Nat) : blk s₀ k + Dl s₀ = sblk s₀ k := by
  rw [blk, sblk, Dl, BitVec.add_comm (Dp s₀), BitVec.add_assoc, BitVec.add_comm (Dp s₀), BitVec.sub_add_cancel,
    BitVec.add_comm]

/-- Nothing that writes only `dst` and the scratch buffer changes `src`. -/
theorem UPre.src_kept (hp : UPre s₀) {m : Mem} (hf : Frame [dataR s₀, scrR s₀] s₀.mem m) {k : Nat}
    (hk : k < N s₀) : m.readW (sblk s₀ k) 128 = s₀.mem.readW (sblk s₀ k) 128 :=
  hf.readW (r := ⟨sblk s₀ k, 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.src_data.sub_left (UPre.src_sub hk)
    · exact hp.src_scr.sub_left (UPre.src_sub hk)) (by decide)

end

theorem ea_ix (s : State) (d : Nat) : s.ea (ix d) = s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (d : Int) := by
  simp only [State.ea, ix, BitVec.mul_one]

theorem pre1To_ok (b t : XReg) (hbt : t ≠ b) (d : Nat) (s : State)
    (hd : InRegions (s.rd ++ s.wr) (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 b (ix d), .vop (.vbin .vpxor .l256 b b t)]) s fun s' =>
      s'.lane b 0 = s.mem.readW (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 128 ^^^ s.lane t 0 ∧
      s'.lane b 1 = s.mem.readW (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 16) 128 ^^^ s.lane t 1 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let v := s.mem.readW (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 256
  let s₁ := s.setV .l256 b (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_ix, hd, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨(VOp.vbin .vpxor .l256 b b t).exec s₁, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ?_, by simp [s₁], by simp [s₁], by simp [s₁], by simp [s₁], fun r hr l _ => by
    simp [s₁, State.lane_setV256, hr]⟩
  · simp [s₁, State.lane_setV256, v, load256_lo, VBinOp.sse, hbt]
  · simp [s₁, State.lane_setV256, v, load256_hi, VBinOp.sse, hbt]


theorem preListTo_ok (regs ts : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (hlen : ts.length = regs.length)
    (hdis : ∀ t ∈ ts, t ∉ regs)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32) :
    WP isa (.block (preXor regs ts j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2, s'.lane regs[k] l =
        s.mem.readW (s.gpr .r11 + s.gpr .rcx + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 ^^^ s.lane (ts[k]'(by omega_arith)) l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing ts j s with
  | nil =>
    cases ts with
    | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    | cons _ _ => simp at hlen
  | cons b bs ih =>
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hd hlen
    have htb : t ≠ b := fun h => hdis t List.mem_cons_self (h ▸ List.mem_cons_self)
    rw [preXor, WP.block_append_iff]
    have hd0 := hd 0 (by omega_arith)
    rw [Nat.add_zero] at hd0
    refine WP.mono (pre1To_ok b t htb (32 * j) s hd0) fun s₁ ⟨lo₁, hi₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih ts (j + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega_arith)
        (fun t' ht' hb => hdis t' (List.mem_cons_of_mem _ ht') (List.mem_cons_of_mem _ hb))
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact hd (k + 1) (by omega_arith)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs l hl, addr2 _ _ _ hl]
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [lo₁]
        · simp only [Nat.one_ne_zero, ite_false]; rw [hi₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hkt' : k < ts.length := by omega_arith
        have hkt : ts[k] ≠ b := fun h =>
          hdis _ (List.mem_cons_of_mem _ (List.getElem_mem hkt')) (by rw [h]; exact List.mem_cons_self)
        rw [hb k hk' l hl, show j + 1 + k = j + (k + 1) by omega_arith, o₁ _ hkt l hl]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2 l hl, o₁ r hr.1 l hl]


theorem tPre1To_ok (b : XReg) (d : Nat) (s : State)
    (hd : InRegions (s.rd ++ s.wr) (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 16)
    (he : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad b (ix d), .vbinLoad .vpxor .l128 b b (at_ .rax d)]) s fun s' =>
      s'.xmm b = s.mem.readW (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 128 ^^^
        s.mem.readW (s.gpr .rax + BitVec.ofInt 64 (d : Int)) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.setXmm,
    State.load128, ea_ix, ea_at, hd, he, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp [State.setV], by simp [State.setV], by simp [State.setV], by simp [State.setV],
    fun r h => by simp [State.setV, h]⟩
  simp [State.setV, State.lane, reduceVBinOpSse, XBinOp.eval]


theorem tPreListTo_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (he : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) :
    WP isa (.block (tPre regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.xmm regs[k] =
        s.mem.readW (s.gpr .r11 + s.gpr .rcx + BitVec.ofNat 64 (16 * (j + k))) 128 ^^^
          s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hd he
    rw [tPre, WP.block_append_iff]
    have hd0 := hd 0 (by omega_arith)
    have he0 := he 0 (by omega_arith)
    rw [Nat.add_zero] at hd0 he0
    refine WP.mono (tPre1To_ok b (16 * j) s hd0 he0) fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact hd (k + 1) (by omega_arith))
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact he (k + 1) (by omega_arith)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, v₁, ofInt_natCast]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega_arith]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2, o₁ r hr.1]


end VG.Proof.AesXts.X86_64.VaesTo

/-! ## One-pass XTS-AES on x86-64, out of place: eight blocks at a time

`GInv`, `Stable`, `group_wp` and `groups_wp` of `Proof/AesXts/X86_64/Vaes/`,
for the out-of-place functions: `rcx` holds `src - dst` (`GInv.rcx`), and
the first `c` blocks of `dst` are XTS's of those of `src` (`outBlk`), the
rest as they were.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Impl.AesXts.X86_64Vaes (bufOff postXor steps regs4 tws constK ldT stT)
open VG.Impl.AesXts.X86_64VaesTo (group preXor)
open VG.Proof.AesXts (b16 next_b8)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast)
open VG.Proof.AesXts.X86_64.Vaes (slot bufR Blk8 TwR stF xts_word bytesAt_b16 next_add stepW tws_regs4
  postList_ok stepsN_ok ldT_ok stT_ok constK_ok)

/-- What the rounds need is kept by writes to `dst` and the tweaks. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → s'.gpr .rdi = s.gpr .rdi → s'.gpr .rsi = s.gpr .rsi → s'.gpr .r8 = s.gpr .r8 →
    s'.gpr .r10 = s.gpr .r10 → s'.rd = s.rd → s'.wr = s.wr → Frame [dataR s₀, bufR s₀] s.mem s'.mem → KP s'

/-- Block `k` of `src` after XTS. -/
abbrev outBlk (enc : Bool) (s₀ : State) (k : Nat) : List Byte :=
  Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k) (bytesAt s₀.mem (sblk s₀ k) 16)

structure GInv (enc : Bool) (KP : State → Prop) (s₀ : State) (b c : Nat) (s : State) : Prop where
  kp : KP s
  le : c ≤ N s₀
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N s₀ - c)
  r11 : s.gpr .r11 = blk s₀ c
  r10 : s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)
  rcx : s.gpr .rcx = Dl s₀
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  data : ∀ k < N s₀, bytesAt s.mem (blk s₀ k) 16 = if k < c then outBlk enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16
  buf : ∀ j < 8, bytesAt s.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j)
  rdx : s.gpr .rdx = Iv s₀

section
variable {s₀ : State}

/-- With `dst + 16 c` in `r11` and `src - dst` in `rcx`, block `c + k` of `src`. -/
theorem ix_sblk {s : State} {c : Nat} (h11 : s.gpr .r11 = blk s₀ c) (hcx : s.gpr .rcx = Dl s₀) (o k : Nat)
    (ho : 16 * c + o = 16 * (c + k)) : s.gpr .r11 + s.gpr .rcx + BitVec.ofNat 64 o = sblk s₀ (c + k) := by
  have e : blk s₀ c + BitVec.ofNat 64 o = blk s₀ (c + k) := by
    rw [blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add, ho]
  rw [h11, hcx, BitVec.add_assoc, BitVec.add_comm (Dl s₀), ← BitVec.add_assoc, e, sblk_eq]

/-- The `n` blocks of `src` from block `c` can be read. -/
theorem UPre.ix_in (hp : UPre s₀) {s : State} {c : Nat} (h11 : s.gpr .r11 = blk s₀ c) (hcx : s.gpr .rcx = Dl s₀)
    (hrd : s.rd = s₀.rd) {o n : Nat} (hn : c * 16 + o + n ≤ 16 * N s₀) (hk : o % 16 = 0) :
    InRegions (s.rd ++ s.wr) (s.gpr .r11 + s.gpr .rcx + BitVec.ofInt 64 (o : Int)) n := by
  have := hp.src_wrap
  have := hp.n_lt
  refine ⟨srcR s₀, List.mem_append_left _ (by rw [hrd, hp.rd]; simp), ?_⟩
  rw [ofInt_natCast, ix_sblk h11 hcx o (o / 16) (by omega), sblk]
  exact Offset.contains_base _ (by omega) (by omega)

end

/-- One group of eight blocks. -/
theorem group_wp {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk8 enc f8 KP s₀) {b c : Nat} (hc : c + 8 ≤ N s₀) {s : State}
    (h : GInv enc KP s₀ b c s) (ht : TwR s₀ c s) :
    WP isa (group f8) s fun s' =>
      (GInv enc KP s₀ b (c + 8) s' ∧ TwR s₀ (c + 8) s') ∧ s'.cf = some (decide (N s₀ - (c + 8) < 8)) := by
  have hw := hp.data_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have inD : ∀ k < 4, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((32 * (0 + k) : Nat) : Int)) 32 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [h.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  -- The blocks of `src`, with the tweaks XORed in.
  refine WP.seq (WP.mono (preListTo_ok regs4 tws 0 s (by decide) rfl tws_regs4
    (fun k hk => hp.ix_in h.r11 h.rcx h.rd (by have : regs4.length = 4 := rfl; omega) (by omega)))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ h.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  have o₂ : ∀ r, r ∉ regs4 → r ≠ .xmm8 → ∀ l < 2, s₂.lane r l = s.lane r l := fun r hr h8 l hl => by
    rw [f₂.lane r (by simp [h8, hr]) l hl, x₁ r hr l hl]
  -- The tweaks XORed in again, and the blocks stored to `dst`.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (postList_ok regs4 tws 0 s₂ (by decide) rfl tws_regs4
    (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (by rw [g₂, h.r11, hp.blk_toNat (by omega)]; show _ + 32 * (0 + 4) ≤ _; omega))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, h.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 32 * regs4.length = 128 from rfl] at f₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have o₃ : ∀ r, r ∉ regs4 → r ≠ .xmm8 → ∀ l < 2, s₃.lane r l = s.lane r l := fun r hr h8 l hl => by
    rw [x₃ r hr l hl, o₂ r hr h8 l hl]
  have hK₃ : ∀ l < 2, qword (s₃.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [o₃ _ (by decide) (by decide) l hl]; exact ht.k87 l hl
  -- The tweaks times `α⁸`.
  rw [WP.block_append_iff]
  refine WP.mono (stepsN_ok tws (by decide) (by decide) (by decide) s₃ hK₃)
    fun s₄ ⟨e₄, g₄, m₄, rd₄, wr₄, x₄⟩ => ?_
  have g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  have kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) rd₄ wr₄
    (by rw [m₄]; exact Frame.refl _ _)
  have hK₄ : ∀ l < 2, qword (s₄.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [x₄ _ (by decide) (by decide) l hl]; exact hK₃ l hl
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem := by
    rw [m₄]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 8 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [m₄]
    by_cases hin : c ≤ k ∧ k < c + 8
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
      have hi : i < 8 := by omega
      have hkk : i / 2 < regs4.length := by have : regs4.length = 4 := rfl; omega
      have hkt : i / 2 < tws.length := by have : tws.length = 4 := rfl; omega
      have hl : i % 2 < 2 := Nat.mod_lt _ (by decide)
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (32 * (0 + i / 2) + 16 * (i % 2)) := by
        rw [h.r11, blk_lane]; congr 2; omega
      have sb : s.gpr .r11 + s.gpr .rcx + BitVec.ofNat 64 (32 * (0 + i / 2) + 16 * (i % 2)) = sblk s₀ (c + i) :=
        ix_sblk h.r11 h.rcx _ i (by omega)
      rw [g₂] at e₃
      rw [bytesAt_b16, ab, e₃ _ hkk _ hl, ← ab]
      have hT : s₂.lane tws[i / 2] (i % 2) = s.lane tws[i / 2] (i % 2) :=
        o₂ _ (tws_regs4 _ (List.getElem_mem hkt)) (by
          have : tws[i / 2] ∈ tws := List.getElem_mem hkt
          intro h8; rw [h8] at this; exact absurd this (by decide)) _ hl
      have e1 := e₁ _ hkk _ hl
      rw [sb, hp.src_kept h.frame (by omega)] at e1
      have hc' : st (s₂.lane regs4[i / 2] (i % 2)) = stF enc (R s₀) (wK s₀)
          (st (s₀.mem.readW (sblk s₀ (c + i)) 128 ^^^ s.lane tws[i / 2] (i % 2))) :=
        (e₂ _ (List.getElem_mem hkk) _ hl).trans (congrArg (fun v => stF enc (R s₀) (wK s₀) (st v)) e1)
      rw [hT]
      refine (xts_word enc (R s₀) (wK s₀) _ _ _ hc').trans ?_
      rw [← bytesAt_b16, ht.tw _ hkt _ hl, show c + (2 * (i / 2) + i % 2) = c + i by omega]
      simp only [show c + i < c + 8 by omega, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), h.data k hk]
      by_cases hlt : k < c
      · simp only [hlt, ite_true, show k < c + 8 by omega]
      · simp only [hlt, ite_false, show ¬ k < c + 8 by omega]
  have hbuf : ∀ j < 8, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := by
    intro j hj
    rw [m₄, AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right (slot_scr (j := j) (by omega))).symm) (by decide),
      h.buf j hj]
  have htw : ∀ k (hk : k < tws.length), ∀ l < 2,
      b16 (s₄.lane tws[k] l) = Spec.Xts.next (iv0 s₀) (c + 8 + (2 * k + l)) := by
    intro k hk l hl
    have hm : tws[k] ∈ tws := List.getElem_mem hk
    rw [e₄ _ hm l hl, o₃ _ (tws_regs4 _ hm) (by intro h8; rw [h8] at hm; exact absurd hm (by decide)) l hl,
      stepW, ← next_b8, ht.tw k hk l hl, ← next_add]
    congr 1; omega
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, h.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, h.wr]
  -- `add r11, 128`, `sub r9, 8` and `cmp r9, 8`.
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', h.r11]
  have hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', h.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hadd : blk s₀ c + 128 = blk s₀ (c + 8) := by
    rw [blk, blk, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 128 = 16 * (c + 8) by omega]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', h.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', h.r10], by simp [g₄', h.rcx],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', h.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₄', h.rdx]⟩, ⟨htw, hK₄⟩⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 8) < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- `GInv` is kept by any change of registers it does not name. -/
theorem GInv.congr {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {b c : Nat} {s s' : State}
    (h : GInv enc KP s₀ b c s) (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : GInv enc KP s₀ b c s' where
  kp := hst s s' h.kp (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide)) hrd hwr
    (by rw [hm]; exact Frame.refl _ _)
  le := h.le
  r8 := by rw [hg _ (by decide), h.r8]
  r9 := by rw [hg _ (by decide), h.r9]
  r11 := by rw [hg _ (by decide), h.r11]
  r10 := by rw [hg _ (by decide), h.r10]
  rcx := by rw [hg _ (by decide), h.rcx]
  keep := fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg r h1, h.keep r h1 h2 h3 h4 h5 h6 h7]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := by rw [hm]; exact h.frame
  data := by rw [hm]; exact h.data
  buf := by rw [hm]; exact h.buf
  rdx := by rw [hg _ (by decide), h.rdx]

/-- The tweak registers from the buffer: `TwR 0`. -/
theorem ldT_twr {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) (hst : Stable KP s₀) {s : State}
    (h : GInv enc KP s₀ 0 0 s) (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87) :
    WP isa (.block (ldT tws 0)) s fun s' => GInv enc KP s₀ 0 0 s' ∧ TwR s₀ 0 s' := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine WP.mono (Vaes.ldT_ok tws 0 s (by decide) fun k hk => inRegions_wr ⟨scrR s₀, by rw [hW]; simp, by
      rw [h.r8, ofInt_natCast]
      rw [show tws.length = 4 from rfl] at hk
      exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩)
    fun s' ⟨e, g, m, rd, wr, x⟩ => ?_
  refine ⟨h.congr hst (fun r _ => by rw [g]) m rd wr, ⟨fun k hk l hl => ?_, fun l hl => by
    rw [x _ (by decide) l hl]; exact hK l hl⟩⟩
  have hk4 : k < 4 := hk
  rw [e k hk l hl, h.r8, show bufOff + 32 * (0 + k) + 16 * l = bufOff + 16 * (2 * k + l) by omega,
    ← bytesAt_b16, h.buf _ (by omega)]

/-- The tweak registers back to the buffer: `GInv c c`. -/
theorem stT_ginv {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) (hst : Stable KP s₀) {c : Nat}
    {s : State} (h : GInv enc KP s₀ 0 c s) (ht : TwR s₀ c s) :
    WP isa (.block (stT tws 0)) s (GInv enc KP s₀ c c) := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine WP.mono (Vaes.stT_ok tws 0 s (fun k hk => ⟨scrR s₀, by rw [hW]; simp, by
      rw [h.r8, ofInt_natCast]
      rw [show tws.length = 4 from rfl] at hk
      exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩)
      (by rw [h.r8]; simp only [bufOff]; have : tws.length = 4 := rfl; omega))
    fun s' ⟨e, f, g, rd, wr, _⟩ => ?_
  rw [h.r8, Nat.mul_zero, Nat.add_zero, show 32 * tws.length = 128 from rfl] at f
  rw [h.r8] at e
  have fb : Frame [bufR s₀] s.mem s'.mem := f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, Region.sub_prefix (by decide)⟩
  have fs : Frame [scrR s₀] s.mem s'.mem := fb.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, buf_scr⟩
  have hbd : ∀ k < N s₀, ∀ r ∈ [bufR s₀], Region.Disjoint ⟨blk s₀ k, 16⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right buf_scr
  exact ⟨hst s s' h.kp (by rw [g]) (by rw [g]) (by rw [g]) (by rw [g]) rd wr (fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, fun _ h => h⟩),
    h.le, by rw [g, h.r8], by rw [g, h.r9], by rw [g, h.r11], by rw [g, h.r10], by rw [g, h.rcx],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [g, h.keep r h1 h2 h3 h4 h5 h6 h7], by rw [rd, h.rd], by rw [wr, h.wr],
    h.frame.trans (fs.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩),
    fun k hk => by rw [AesCbc.X86_64.bytesAt_frame fb (hbd k hk) (by decide), h.data k hk],
    fun j hj => by
      have hk : j / 2 < tws.length := by have : tws.length = 4 := rfl; omega
      rw [bytesAt_b16, slot, show bufOff + 16 * j = bufOff + 32 * (0 + j / 2) + 16 * (j % 2) by omega,
        e _ hk _ (Nat.mod_lt _ (by decide)), ht.tw _ hk _ (Nat.mod_lt _ (by decide))]
      congr 1; omega,
    by rw [g, h.rdx]⟩

/-- The eight-block loop, if eight blocks are left. -/
theorem groups_wp {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk8 enc f8 KP s₀) {s : State} (h : GInv enc KP s₀ 0 0 s)
    (hcf : s.cf = some (decide (N s₀ < 8))) :
    WP isa (Impl.AesXts.X86_64VaesTo.loop8 f8) s fun s' => ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c s' := by
  refine WP.ite (decide (N s₀ < 8)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨0, by simpa using hb, h⟩
  · simp at hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (constK_ok s) fun s₁ ⟨k₁, g₁, m₁, rd₁, wr₁⟩ => ?_
    have h₁ : GInv enc KP s₀ 0 0 s₁ := h.congr hst (fun r h1 => g₁ r h1) m₁ rd₁ wr₁
    refine WP.mono (ldT_twr hp hst h₁ k₁) fun s₂ ⟨h₂, t₂⟩ => ?_
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ GInv enc KP s₀ 0 c t ∧ TwR s₀ c t
    have hstep : ∀ m t, I m t → WP isa (group f8) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ 0 c t' ∧ TwR s₀ c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI, hT⟩
      refine WP.mono (group_wp hp hst hf hc hI hT) fun t' ⟨⟨hI', hT'⟩, hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 8) < 8
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI', hT'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI', hT'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I hstep (N s₀) s₂ ⟨0, by simp, by omega, h₂, t₂⟩)
      fun s₃ ⟨c, hc, h₃, t₃⟩ => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (stT_ginv hp hst h₃ t₃) fun s₄ h₄ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
    exact ⟨c, hc, h₄.congr hst (fun _ _ => rfl) rfl rfl rfl⟩

end VG.Proof.AesXts.X86_64.VaesTo

/-! ## One-pass XTS-AES on x86-64, out of place: the arguments and the first eight tweaks

`enterTo` keeps `src - dst` at `scratch + 248` (`SInv.dl`) and moves the
arguments as `enter` does, with `dst` as the data pointer (`SInv.r11`);
`gen` then stores the tweaks of blocks `0 … 7` at `scratch + 256`, as in
`Proof/AesXts/X86_64/Vaes/Setup.lean`, and leaves `src - dst` where it was.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesXts.X86_64Vaes (bufOff enter genStep gen)
open VG.Impl.AesXts.X86_64VaesTo (dOff enterTo)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)
open VG.Proof.AesXts.X86_64.Vaes (slot mulAr_ok)

/-- Where `src - dst` is kept. -/
abbrev dAddr (s₀ : State) : Addr := S s₀ + BitVec.ofNat 64 dOff

/-- During `gen`, after `n` tweaks. -/
structure SInv (s₀ : State) (n : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N s₀)
  r11 : s.gpr .r11 = Dp s₀
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem
  buf : ∀ j < n, bytesAt s.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) j
  rdx : s.gpr .rdx = Iv s₀
  tw : tw (s.gpr .rax) (s.gpr .rcx) = Spec.Xts.next (iv0 s₀) n
  dl : s.mem.readW (dAddr s₀) 64 = Dl s₀

/-- After `gen`: the tweaks, and the last round key's address in `r10`. -/
def SInvK (s₀ s : State) : Prop := SInv s₀ 8 s ∧ s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)

theorem dAddr_scr {s₀ : State} : Region.Sub ⟨dAddr s₀, 8⟩ (scrR s₀) := UPre.scr_sub (by decide)

theorem genStep_ok {s₀ : State} (hp : UPre s₀) {n : Nat} (hn : n < 8) {s : State} (h : SInv s₀ n s) :
    WP isa (.block (genStep n)) s (SInv s₀ (n + 1)) := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have a0 : s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 16 * n : Nat) : Int) = slot s₀ n := by
    rw [h.r8, ofInt_natCast]
  have a8 : s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 16 * n + 8 : Nat) : Int) = slot s₀ n + BitVec.ofNat 64 8 := by
    rw [h.r8, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
  have in0 : InRegions s.wr (slot s₀ n) 8 := ⟨scrR s₀, by rw [hW]; simp,
    Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  have in8 : InRegions s.wr (slot s₀ n + BitVec.ofNat 64 8) 8 := ⟨scrR s₀, by rw [hW]; simp, by
    rw [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  rw [genStep, WP.block_append_iff]
  have st₁ : WP isa (.block [.store (at_ .r8 (bufOff + 16 * n)) .rax, .store (at_ .r8 (bufOff + 16 * n + 8)) .rcx]) s
      fun s₁ => s₁.mem = (s.mem.writeW (slot s₀ n) (s.gpr .rax)).writeW (slot s₀ n + BitVec.ofNat 64 8) (s.gpr .rcx) ∧
        s₁.gpr = s.gpr ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_at, a0, a8, in0, in8, ↓reduceIte,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial⟩
  refine WP.mono st₁ fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_
  obtain ⟨s₂, run₂, g₂, rax₂, rcx₂, m₂, rd₂, wr₂⟩ := mulAr_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have fS : Frame [⟨slot s₀ n, 16⟩] s.mem s₂.mem := by rw [m₂, m₁]; exact AesCbc.frame_store2 _ _ _
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₂ r h1 h2 h3, g₁]
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide), h.r8], by rw [hg _ (by decide) (by decide) (by decide), h.r9],
    by rw [hg _ (by decide) (by decide) (by decide), h.r11],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg r h1 h2 h6, h.keep r h1 h2 h3 h4 h5 h6 h7],
    by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr],
    h.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, slot_scr (j := n) (by omega)⟩), fun j hj => ?_,
    by rw [hg _ (by decide) (by decide) (by decide), h.rdx], ?_, ?_⟩
  · by_cases hjn : j = n
    · subst hjn
      rw [m₂, m₁, Proof.Cmac.bytesAt_store2, ← h.tw]
    · rw [AesCbc.X86_64.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by simp only [bufOff]; omega) (by simp only [bufOff]; omega))
        (by decide), h.buf j (by omega)]
  · rw [rax₂, rcx₂, mulAlpha_le8, g₁, h.tw]; rfl
  · rw [fS.readW (r := ⟨dAddr s₀, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by simp only [dOff, bufOff]; omega) (by simp only [dOff]; omega)
          (by simp only [bufOff]; omega)) (by decide), h.dl]

theorem gen_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : SInv s₀ 0 s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap genStep)) s (SInv s₀ n)
  | 0, _ => WP.block_nil h
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (gen_ok hp h n (by omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact genStep_ok hp (by omega) h₁

/-- The last round key's address, `rdi + 16 · rounds`, into `r10`. -/
theorem lastKey_ok {s₀ : State} {s : State} (h : SInv s₀ 8 s) :
    WP isa (.block ([.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] : List Instr)) s
      (SInvK s₀) := by
  have hrsi := h.keep .rsi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrdi := h.keep .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setFlags, State.setReg, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.r8], by simp [h.r9], by simp [h.r11], fun r h1 h2 h3 h4 h5 h6 h7 => by
    simp [h6, h.keep r h1 h2 h3 h4 h5 h6 h7], h.rd, h.wr, h.frame, h.buf, by simp [h.rdx], by simpa using h.tw,
    h.dl⟩, ?_⟩
  simp only [↓reduceIte, hrsi, hrdi, W, R]
  bv_omega

theorem gen_all_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : SInv s₀ 0 s) :
    WP isa (.block gen) s (SInvK s₀) := by
  rw [gen, WP.block_append_iff]
  exact WP.mono (gen_ok hp h 8 (Nat.le_refl _)) fun s₁ h₁ => lastKey_ok h₁

/-- `src - dst` kept, and the arguments moved. -/
theorem enterTo_ok {s₀ : State} (hp : UPre s₀) : WP isa (.block enterTo) s₀ (SInv s₀ 0) := by
  have hsw := hp.scr_wrap
  have hD : InRegions s₀.wr (s₀.gpr .r9 + BitVec.ofInt 64 ((dOff : Nat) : Int)) 8 :=
    ⟨scrR s₀, by rw [hp.wr]; simp, by
      rw [ofInt_natCast]; exact Offset.contains_base _ (by simp only [dOff]; omega) (by simp only [dOff]; omega)⟩
  let m₁ := s₀.mem.writeW (dAddr s₀) (Dl s₀)
  have f₁ : Frame [⟨dAddr s₀, 8⟩] s₀.mem m₁ :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hIv8 : InRegions (s₀.rd ++ s₀.wr) (Iv s₀ + BitVec.ofNat 64 8) 8 := ⟨ivR s₀, by rw [hp.wr]; simp, cIv8⟩
  have z0 : BitVec.ofInt 64 ((0 : Nat) : Int) = 0 := rfl
  have z8 : BitVec.ofInt 64 ((8 : Nat) : Int) = BitVec.ofNat 64 8 := rfl
  have hIv : InRegions (s₀.rd ++ s₀.wr) (Iv s₀) 8 := ⟨ivR s₀, by rw [hp.wr]; simp, cIv0⟩
  have hIv0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdx + 0) 8 := by simpa using hIv
  have hiv : bytesAt m₁ (Iv s₀) 16 = iv0 s₀ := AesCbc.X86_64.bytesAt_frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_scr.sub_right dAddr_scr) (by decide)
  apply WP.of_runBlock
  simp only [enterTo, enter, List.cons_append, List.nil_append, reduceCtorEq, ↓reduceIte, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags, State.setReg, State.load64,
    State.store64, ea_at, z0, z8, hIv0, hIv8, hD, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  have ea : s₀.gpr .r9 + BitVec.ofInt 64 ((dOff : Nat) : Int) = dAddr s₀ := by rw [ofInt_natCast]
  have e0 : s₀.gpr .rdx + 0 = Iv s₀ := by simp
  rw [ea, e0]
  refine ⟨by simp, by simp, by simp, fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h2, h4, h5, h7], rfl, rfl,
    f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, dAddr_scr⟩,
    fun j hj => absurd hj (Nat.not_lt_zero _), by simp, ?_, ?_⟩
  · simp only [reduceCtorEq, ↓reduceIte]
    rw [tw_readW]; exact hiv
  · exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.AesXts.X86_64.VaesTo

/-! ## One-pass XTS-AES on x86-64, out of place: the blocks left

`tbody_ok` and `tail_wp` of `Proof/AesXts/X86_64/Vaes/Tail.lean`, with each
block loaded from `src` (`tPreListTo_ok`) and stored to `dst`.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Impl.AesXts.X86_64Vaes (bufOff tPost)
open VG.Impl.AesXts.X86_64VaesTo (tPre)
open VG.Proof.AesXts (b16)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast XFrame)
open VG.Proof.AesXts.X86_64.Vaes (slot Blk1 stF xts_word bytesAt_b16 tPostList_ok)

/-- In the tail: `rax` points at the tweak of block `c`. -/
structure TInv (enc : Bool) (KP : State → Prop) (s₀ : State) (b c : Nat) (s : State) : Prop where
  g : GInv enc KP s₀ b c s
  bc : b ≤ c
  lt : N s₀ < b + 8
  rax : s.gpr .rax = slot s₀ (c - b)

/-- Block `c` through `f` on `xmm0`, and the pointers advanced. -/
theorem tbody_ok {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk1 enc f KP s₀) (rs : List XReg) (n : Nat)
    (hrs : rs = [.xmm0] ∧ n = 1)
    {b c : Nat} (hc : c + n ≤ N s₀) {s : State} (h : TInv enc KP s₀ b c s) :
    WP isa (.seq (.block (tPre rs 0)) (.seq (f rs) (.block (tPost rs 0 ++
        ([.alu .add .r11 (.imm (BitVec.ofNat 32 (16 * n))), .alu .add .rax (.imm (BitVec.ofNat 32 (16 * n))),
          .alu .sub .r9 (.imm (BitVec.ofNat 32 n))] : List Instr))))) s fun s' =>
      TInv enc KP s₀ b (c + n) s' ∧ s'.zf = some (decide (N s₀ - (c + n) = 0)) := by
  obtain ⟨hrs1, hn1⟩ := hrs
  have hlen : rs.length = n := by rw [hrs1, hn1]; rfl
  have hnd : rs.Nodup := by rw [hrs1]; decide
  have hg := h.g
  have hw := hp.data_wrap
  have hsw := hp.scr_wrap
  have hlt := h.lt
  have hbc := h.bc
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  have hnl := hp.n_lt
  have inD : ∀ k < rs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [hg.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  have inT : ∀ k < rs.length, InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨scrR s₀, by rw [hW]; simp, ?_⟩
    rw [h.rax, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (tPreListTo_ok rs 0 s hnd
    (fun k hk => hp.ix_in hg.r11 hg.rcx hg.rd (by omega) (by omega))
    (fun k hk => inRegions_wr (inT k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ hg.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  have hf' : WP isa (f rs) s₁ fun s' =>
      st (s'.xmm .xmm0) = stF enc (R s₀) (wK s₀) (st (s₁.xmm .xmm0)) ∧ XFrame [.xmm8, .xmm0] s₁ s' := by
    rw [hrs1]; exact hf s₁ kp₁
  refine WP.seq (WP.mono hf' fun s₂ ⟨e₂', f₂⟩ => ?_)
  have e₂ : ∀ b ∈ rs, st (s₂.xmm b) = stF enc (R s₀) (wK s₀) (st (s₁.xmm b)) := fun b hb => by
    rw [hrs1] at hb; simp only [List.mem_singleton] at hb; subst hb; exact e₂'
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  -- The tweaks XORed in again, and the blocks stored.
  rw [WP.block_append_iff]
  have hr11N : (s.gpr .r11).toNat = (Dp s₀).toNat + 16 * c := by rw [hg.r11]; exact hp.blk_toNat (by omega)
  refine WP.mono (tPostList_ok rs 0 s₂ hnd (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (fun k hk => by rw [rd₂, wr₂, g₂]; exact inRegions_wr (inT k hk)) (by rw [g₂, hr11N]; omega)
    (fun k hk => by
      rw [g₂, h.rax, hg.r11, Nat.mul_zero, BitVec.add_zero, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hp.data_scr.sub_left (group_data_n (s₀ := s₀) (c := c) (n := rs.length) (by omega))).sub_right
        (UPre.scr_sub (by simp only [bufOff]; omega))).symm))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, hg.r11, Nat.mul_zero, BitVec.add_zero, m₂, hlen] at f₃
  rw [g₂, m₂] at e₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hdata : ∀ k < N s₀, bytesAt s₃.mem (blk s₀ k) 16 = if k < c + n then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    by_cases hin : c ≤ k ∧ k < c + n
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
      have hi : i < rs.length := by omega
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [hg.r11, blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      have sl : slot s₀ (c - b + i) = s.gpr .rax + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [h.rax, slot, slot, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rw [bytesAt_b16, ab, e₃ _ hi, ← sl, ← ab]
      have e1 := e₁ _ hi
      rw [ix_sblk hg.r11 hg.rcx _ i (by omega), hp.src_kept hg.frame (by omega), ← sl] at e1
      have hc' : st (s₂.xmm rs[i]) = stF enc (R s₀) (wK s₀)
          (st (s₀.mem.readW (sblk s₀ (c + i)) 128 ^^^ s.mem.readW (slot s₀ (c - b + i)) 128)) := by
        rw [e₂ _ (List.getElem_mem hi), e1]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', ← bytesAt_b16, ← bytesAt_b16, hg.buf _ (by omega),
        show b + (c - b + i) = c + i by omega]
      simp only [show c + i < c + n by omega, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), hg.data k hk]
      by_cases hlt' : k < c
      · simp only [hlt', ite_true, show k < c + n by omega]
      · simp only [hlt', ite_false, show ¬ k < c + n by omega]
  have hbuf : ∀ j < 8, bytesAt s₃.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := fun j hj => by
    rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right (slot_scr (j := j) (by omega))).symm) (by decide), hg.buf j hj]
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₃.mem :=
    hg.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hrd : s₃.rd = s₀.rd := by rw [rd₃, rd₂, hg.rd]
  have hwr : s₃.wr = s₀.wr := by rw [wr₃, wr₂, hg.wr]
  -- `add r11, 16 n`, `add rax, 16 n` and `sub r9, n`.
  have e16 : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * n)) = BitVec.ofNat 64 (16 * n) := by rw [hn1]; decide
  have e1 : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by rw [hn1]; decide
  have hr11 : s₃.gpr .r11 = blk s₀ c := by rw [g₃', hg.r11]
  have hrax : s₃.gpr .rax = slot s₀ (c - b) := by rw [g₃', h.rax]
  have hr9 : s₃.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₃', hg.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - BitVec.ofNat 64 n = BitVec.ofNat 64 (N s₀ - (c + n)) := by
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hadd : blk s₀ c + BitVec.ofNat 64 (16 * n) = blk s₀ (c + n) := by
    rw [blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * c + 16 * n = 16 * (c + n) by omega]
  have hadd' : slot s₀ (c - b) + BitVec.ofNat 64 (16 * n) = slot s₀ (c + n - b) := by
    rw [slot, slot, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, hr11, hrax, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₃ _ kp₃ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₃', hg.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₃', hg.r10], by simp [g₃', hg.rcx],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h5, h7, g₃', hg.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₃', hg.rdx]⟩, by omega, hlt, by simp; exact hadd'⟩, ?_⟩
  simp only [hsub]
  exact Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (by have := (s₀.gpr .r8).isLt; omega)

open VG.Impl.AesXts.X86_64VaesTo (tail tail1)

/-- The blocks left, one at a time. -/
theorem tail_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk1 enc f KP s₀) {c : Nat} (hlt : N s₀ < c + 8) {s : State}
    (h : GInv enc KP s₀ c c s) :
    WP isa (tail f) s (TInv enc KP s₀ c (N s₀)) := by
  have hle := h.le
  have hn := (s₀.gpr .r8).isLt
  -- `mov rax, r8`, `add rax, 256` and `test r9, r9`.
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have hr8 := h.r8
  have hr9 := h.r9
  have st₁ : WP isa (.block [.mov .rax (.reg .r8), .alu .add .rax (.imm 256), .alu .test .r9 (.reg .r9)]) s
      fun s₁ => TInv enc KP s₀ c c s₁ ∧ s₁.zf = some (decide (N s₀ - c = 0)) := by
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      arithFlags, State.setFlags, State.setReg, e256, hr8, hr9, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨hst s _ h.kp (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), h.le,
      by simp [hr8], by simp [hr9], by simp [h.r11], by simp [h.r10], by simp [h.rcx],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h.keep r h1 h2 h3 h4 h5 h6 h7],
      h.rd, h.wr, h.frame, h.data, h.buf, by simp [h.rdx]⟩, Nat.le_refl _, hlt, ?_⟩, ?_⟩
    · simp only [ite_true, Nat.sub_self, slot, Nat.mul_zero, Nat.add_zero, bufOff]; rfl
    · simp only [BitVec.and_self]
      rw [Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (k := N s₀ - c) (by omega)]
  refine WP.seq (WP.mono st₁ fun s₃ ⟨h₃, zf₃⟩ => ?_)
  -- One block at a time.
  refine WP.ite (decide (N s₀ - c = 0)) (by simp [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · simp at hz
    exact WP.block_nil (by rw [show N s₀ = c by omega]; exact h₃)
  · simp at hz
    let I : Nat → State → Prop := fun m t => ∃ d, m = N s₀ - d ∧ d < N s₀ ∧ TInv enc KP s₀ c d t
    have hstep : ∀ m t, I m t → WP isa (tail1 f) t (fun t' =>
        (eval .ne t' = some false ∧ TInv enc KP s₀ c (N s₀) t') ∨
        (eval .ne t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨d, rfl, hd, hI⟩
      refine WP.mono (tbody_ok hp hst hf [.xmm0] 1 ⟨rfl, rfl⟩ (by omega) hI) fun t' ⟨hI', zf'⟩ => ?_
      by_cases hz' : N s₀ - (d + 1) = 0
      · exact .inl ⟨by simp [eval, zf', hz'], by rw [show N s₀ = d + 1 by omega]; exact hI'⟩
      · exact .inr ⟨by simp [eval, zf', hz'], N s₀ - (d + 1), by omega, d + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (N s₀ - c) s₃ ⟨c, rfl, by omega, h₃⟩

end VG.Proof.AesXts.X86_64.VaesTo

/-! ## One-pass XTS-AES on x86-64, out of place: the whole function

`crypt_wp`: `Impl.AesXts.X86_64VaesTo.crypt pre L f` meets the contract
`To.xtsToX86_64 enc`, from the same hypotheses as `Vaes.crypt_wp`: `pre`
sets up what the rounds need (`KP`) and keeps the tweaks and `src - dst`
(`SInvK`), `L` takes groups of eight blocks (`LoopOk`), and `f` computes
the cipher (or its inverse) on `xmm0`.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Impl.AesXts.X86_64Vaes (bufOff finish gen)
open VG.Impl.AesXts.X86_64VaesTo (dOff ldD enterTo crypt loop8)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)
open VG.Proof.AesXts.X86_64.Vaes (slot Blk1 Blk8 getElem_tweaks)

/-- `src - dst` into `rcx`, and `cmp r9, 8`: `GInv 0 0`. -/
theorem ldD_wp {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) (hst : Stable KP s₀) {s : State}
    (hk : SInvK s₀ s) (hkp : KP s) :
    WP isa (.block ldD) s fun s' => GInv enc KP s₀ 0 0 s' ∧ s'.cf = some (decide (N s₀ < 8)) := by
  have h := hk.1
  have hsw := hp.scr_wrap
  have hD : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((dOff : Nat) : Int)) 8 :=
    ⟨scrR s₀, List.mem_append_right _ (by rw [h.wr, hp.wr]; simp), by
      rw [h.r8, ofInt_natCast]
      exact Offset.contains_base _ (by simp only [dOff]; omega) (by simp only [dOff]; omega)⟩
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr9 := h.r9
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  apply WP.of_runBlock
  simp only [ldD, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.setReg, State.load64, ea_at, hD, e8, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨hst s _ hkp (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), Nat.zero_le _,
    by simp [h.r8], by simp [hr9], by simp [h.r11, blk], by simp [hk.2], by rw [h.r8]; exact h.dl,
    fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h2, h.keep r h1 h2 h3 h4 h5 h6 h7], h.rd, h.wr,
    h.frame.mono fun r hr => by simp at hr; simp [hr],
    fun k hk => by
      simp only [Nat.not_lt_zero, ite_false]
      exact AesCbc.X86_64.bytesAt_frame h.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.data_scr.sub_left (UPre.data_sub hk)) (by decide),
    fun j hj => by simp only [Nat.zero_add]; exact h.buf j hj, by simp [h.rdx]⟩, ?_⟩
  simp only [arithFlags, State.setFlags, hr9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The contract, from `GInv … N` and the tweak after the last block stored. -/
theorem post_of {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {b : Nat} {s : State}
    (h : GInv enc KP s₀ b (N s₀) s) (s' : State) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (N s₀))
    (hgs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    gprPreserved s₀ s' ∧ (To.xtsToX86_64 enc).post s₀ s' := by
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, hiv⟩
  · rw [hgs r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [hf.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_iv) (by decide),
      h.frame.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.ret_data
        · exact hp.ret_scr) (by decide)]
  · show Spec.Cbc.blocksAt s'.mem (Dp s₀) (N s₀) = Spec.Xts.crypt (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀)
      (Spec.Cbc.blocksAt s₀.mem (Sr s₀) (N s₀))
    apply List.ext_getElem (by rw [AesXts.length_crypt, AesCbc.length_blocksAt, AesCbc.length_blocksAt])
    intro k h₁ h₂
    have hk : k < N s₀ := by rwa [AesCbc.length_blocksAt] at h₁
    rw [AesCbc.getElem_blocksAt _ _ hk]
    simp only [Spec.Xts.crypt, List.getElem_zipWith]
    rw [getElem_tweaks _ (by rwa [AesCbc.length_blocksAt]), AesCbc.getElem_blocksAt _ _ hk,
      AesCbc.X86_64.bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.iv_data.sub_right (UPre.data_sub hk)).symm)
        (by decide), h.data k hk]
    simp only [hk, ite_true]

/-- The tweak after the last block copied to the tweak pointer. -/
theorem finish_wp {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {b : Nat} {s : State}
    (h : TInv enc KP s₀ b (N s₀) s) :
    WP isa (.block finish) s fun s' => gprPreserved s₀ s' ∧ (To.xtsToX86_64 enc).post s₀ s' := by
  have hg := h.g
  have hsw := hp.scr_wrap
  have hlt := h.lt
  have hbc := h.bc
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  have hR : s.rd ++ s.wr = [schR s₀, srcR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hg.rd, hW, hp.rd]; rfl
  have z0 : BitVec.ofInt 64 ((0 : Nat) : Int) = 0#64 := rfl
  have z8 : BitVec.ofInt 64 ((8 : Nat) : Int) = BitVec.ofNat 64 8 := rfl
  let T := slot s₀ (N s₀ - b)
  have inT0 : InRegions (s.rd ++ s.wr) (s.gpr .rax + 0#64) 8 := ⟨scrR s₀, by rw [hR]; simp, by
    rw [h.rax]; simpa using Offset.contains_base (S s₀) (d := bufOff + 16 * (N s₀ - b)) (n := 8) (k := 2176)
      (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  have inI0 : InRegions s.wr (Iv s₀ + 0#64) 8 := ⟨ivR s₀, by rw [hW]; simp, by simpa using cIv0⟩
  have inI8 : InRegions s.wr (Iv s₀ + BitVec.ofNat 64 8) 8 := ⟨ivR s₀, by rw [hW]; simp, cIv8⟩
  have inT8 : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 8) 8 := ⟨scrR s₀, by rw [hR]; simp, by
    rw [h.rax, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  have hrdx := hg.rdx
  apply WP.of_runBlock
  simp only [finish, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, State.load64, State.store64, ea_at, z0, z8, hrdx, inT0, inT8, inI0, inI8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [BitVec.add_zero]
  have hT8 : Region.Disjoint ⟨T + BitVec.ofNat 64 8, 8⟩ ⟨Iv s₀, 8⟩ := by
    have hiv : Region.Disjoint (scrR s₀) ⟨Iv s₀, 8⟩ :=
      hp.iv_scr.symm.sub_right (Region.sub_prefix (len := 8) (len' := 16) (by decide))
    refine hiv.sub_left ?_
    show Region.Sub ⟨slot s₀ (N s₀ - b) + BitVec.ofNat 64 8, 8⟩ (scrR s₀)
    rw [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.sub_base _ (by simp only [bufOff]; omega)
  have f1 : Frame [⟨Iv s₀, 8⟩] s.mem (s.mem.writeW (Iv s₀) (s.mem.readW T 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [h.rax]
  refine post_of hp hg _ (AesCbc.frame_store2 _ _ _) ?_ fun r hr => ?_
  · rw [Proof.Cmac.bytesAt_store2, f1.readW (r := ⟨T + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hT8) (by decide)]
    rw [← tw, tw_readW, hg.buf _ (by omega), show b + (N s₀ - b) = N s₀ by omega]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- `L` takes groups of eight blocks while eight are left: from `GInv 0 0`,
with `cmp r9, 8` done, to `GInv c c` with fewer than eight left. -/
def LoopOk (enc : Bool) (L : Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, GInv enc KP s₀ 0 0 s → s.cf = some (decide (N s₀ < 8)) →
    WP isa L s fun s' => ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c s'

theorem loop8_ok {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf8 : Blk8 enc f8 KP s₀) : LoopOk enc (loop8 f8) KP s₀ :=
  fun _ h hcf => groups_wp hp hst hf8 h hcf

/-- The function's body, with at least one block. -/
theorem body_wp {enc : Bool} {KP : State → Prop} {pre L : Prog isa} {f : List XReg → Prog isa} {s₀ : State}
    (hp : UPre s₀) (hst : Stable KP s₀) (hL : LoopOk enc L KP s₀) (hf : Blk1 enc f KP s₀)
    (hpre : ∀ s, SInvK s₀ s → WP isa pre s fun s' => SInvK s₀ s' ∧ KP s') :
    WP isa (.seq (.block (enterTo ++ gen)) (.seq pre (.seq (.block ldD)
      (.seq L (.seq (Impl.AesXts.X86_64VaesTo.tail f) (.block finish)))))) s₀
      fun s' => gprPreserved s₀ s' ∧ (To.xtsToX86_64 enc).post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterTo_ok hp) fun s₁ h₁ => WP.mono (gen_all_ok hp h₁) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (hpre s₂ h₂) fun s₃ ⟨h₃, kp₃⟩ => ?_)
  refine WP.seq (WP.mono (ldD_wp (enc := enc) hp hst h₃ kp₃) fun s₄ ⟨g₄, cf₄⟩ => ?_)
  refine WP.seq (WP.mono (hL s₄ g₄ cf₄) fun s₅ ⟨c, hc, g₅⟩ => ?_)
  exact WP.seq (WP.mono (tail_wp hp hst hf (by omega) g₅) fun s₆ h₆ => finish_wp hp h₆)

/-- The whole function. -/
theorem crypt_wp {enc : Bool} {KP : State → State → Prop} {pre L : Prog isa} {f : List XReg → Prog isa} {s₀ : State}
    (h0 : (To.xtsToX86_64 enc).pre s₀)
    (hst : ∀ s₁ : State, UPre s₁ → Stable (KP s₁) s₁)
    (hL : ∀ s₁ : State, UPre s₁ → LoopOk enc L (KP s₁) s₁)
    (hf : ∀ s₁ : State, UPre s₁ → Blk1 enc f (KP s₁) s₁)
    (hpre : ∀ s₁ : State, UPre s₁ → ∀ s, SInvK s₁ s → WP isa pre s fun s' => SInvK s₁ s' ∧ KP s₁ s') :
    WP isa (crypt pre L f) s₀ fun s' => gprPreserved s₀ s' ∧ (To.xtsToX86_64 enc).post s₀ s' := by
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have st : WP isa (.block [.alu .test .r8 (.reg .r8)]) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.zf = some (decide (N s₀ = 0)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [arithFlags, State.setFlags, BitVec.and_self]
    have e : s₀.gpr .r8 = BitVec.ofNat 64 (N s₀) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [e, Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' hn]
  refine WP.seq (WP.mono st fun s₁ ⟨g, m, rd, wr, zf⟩ => ?_)
  refine WP.ite (decide (N s₀ = 0)) (by simp [eval, zf]) (fun hz => ?_) (fun hz => ?_)
  · simp at hz
    refine WP.block_nil ⟨⟨fun r _ => by rw [g], by rw [m]⟩, ?_, ?_⟩
    · show Spec.Cbc.blocksAt s₁.mem (Dp s₀) (N s₀) = Spec.Xts.crypt _ _ (Spec.Cbc.blocksAt s₀.mem (Sr s₀) (N s₀))
      rw [hz]; rfl
    · show bytesAt s₁.mem (Iv s₀) 16 = Spec.Xts.next _ (N s₀)
      rw [hz, m]; rfl
  · have h1 : (To.xtsToX86_64 enc).pre s₁ := by
      simp only [To.xtsToX86_64, g, rd, wr]; simpa only [To.xtsToX86_64] using h0
    have hp₁ := UPre.of h1
    refine WP.mono (body_wp hp₁ (hst s₁ hp₁) (hL s₁ hp₁) (hf s₁ hp₁) (hpre s₁ hp₁)) fun s' ⟨gp, po⟩ => ?_
    refine ⟨⟨fun r hr => by rw [gp.1 r hr, g], by rw [← m, ← g]; exact gp.2⟩, ?_⟩
    simp only [To.xtsToX86_64, g, m] at po ⊢
    exact po

end VG.Proof.AesXts.X86_64.VaesTo

/-! ## One-pass XTS-AES on x86-64, out of place: what the rounds need

What the rounds need is `Vaes.KPe` and `Vaes.KPd`, as in place: the key
schedule (and for decryption the round keys through `aesimc` at the start of
the scratch buffer), kept by writes to `dst` and the tweaks (`kpe_stable`,
`kpd_stable`), and set up after `gen` (`kpe_pre`, `imc_pre`, which keeps
`src - dst` at `scratch + 248`, above the round keys). `encryptVaes_wp`
and `decryptVaes_wp`: the VAES functions meet `To.xtsToX86_64`.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64.AesNi (Keys DKeys imcKeys_ok dKeys_of_imc ofInt_natCast contains_offset)
open VG.Proof.AesXts.X86_64.Vaes (KPe KPd rsi_ofNat)
open VG.Impl.AesXts.X86_64Vaes (regs4 bufOff)
open VG.Impl.AesXts.X86_64VaesTo (dOff)

theorem kpe_stable {s₀ : State} (hp : UPre s₀) : Stable (KPe s₀) s₀ :=
  fun s s' ⟨hK, hrdi, hrsi, hr10⟩ g1 g2 _ g4 hrd hwr hf =>
    ⟨Aes.X86_64.AesNi.Ecb.keys_congr hK g1 hrd hwr (by
        rw [hrdi]
        exact AesCbc.X86_64.bytesAt_frame hf (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.sch_data.sub_left (Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)))
          · exact (hp.sch_scr.sub_left (Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega))).sub_right
              buf_scr) (by rcases hp.rounds with h | h | h <;> omega)),
      by rw [g1, hrdi], by rw [g2, hrsi], by rw [g4, g1, hr10]⟩

theorem keys_entry {s₀ : State} (hp : UPre s₀) : Keys (R s₀) (wK s₀) s₀ :=
  ⟨rfl, by rcases hp.rounds with h | h | h <;> omega, fun j hj => ⟨schR s₀, by simp [hp.rd], by
    rw [ofInt_natCast]; exact contains_offset (by rcases hp.rounds with h | h | h <;> omega)
      (by rcases hp.rounds with h | h | h <;> omega)⟩⟩

/-- The key schedule, as encryption's rounds need it, after the setup. -/
theorem kpe_pre {s₁ : State} (hp₁ : UPre s₁) {s : State} (h : SInvK s₁ s) : KPe s₁ s := by
  have hrdi : s.gpr .rdi = W s₁ := h.1.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  refine ⟨Aes.X86_64.AesNi.Ecb.keys_congr (keys_entry hp₁) hrdi h.1.rd h.1.wr ?_, hrdi,
    h.1.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [h.2, hrdi]⟩
  exact AesCbc.X86_64.bytesAt_frame h.1.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp₁.sch_scr.sub_left (Region.sub_prefix (by rcases hp₁.rounds with h | h | h <;> omega)))
    (by rcases hp₁.rounds with h | h | h <;> omega)

theorem kpd_stable {s₀ : State} (hp : UPre s₀) : Stable (KPd s₀) s₀ :=
  fun s s' ⟨hK, hrdi, hrsi, hr8, hr10⟩ g1 g2 g3 g4 hrd hwr hf => by
    have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
    refine ⟨Aes.X86_64.AesNi.Ecb.dkeys_congr hK g1 g3 hrd hwr (by
        rw [hrdi]
        exact AesCbc.X86_64.bytesAt_frame hf (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.sch_data.sub_left (Region.sub_prefix hR))
          · exact (hp.sch_scr.sub_left (Region.sub_prefix hR)).sub_right buf_scr) (by omega))
        fun j h1 h2 => ?_,
      by rw [g1, hrdi], by rw [g2, hrsi], by rw [g3, hr8], by rw [g4, g1, hr10]⟩
    have hj : 16 * j + 16 ≤ 224 := by rcases hp.rounds with h | h | h <;> omega
    have := hp.scr_wrap
    rw [hr8, ofInt_natCast]
    exact hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 (16 * j), 16⟩) (w := 128) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.data_scr.sub_right (UPre.scr_sub (by omega))).symm
        · exact Offset.disjoint _ (by simp only [bufOff]; omega) (by omega) (by simp only [bufOff]; omega))
      (by decide)

/-- The round keys through `aesimc` at the scratch buffer, below `src - dst`
and the tweaks: what decryption's rounds need. -/
theorem imc_pre {s₁ : State} (hp₁ : UPre s₁) {s : State} (h : SInvK s₁ s) :
    WP isa Impl.Aes.X86_64.AesNi.imcKeys s fun s' => SInvK s₁ s' ∧ KPd s₁ s' := by
  have hsw := hp₁.scr_wrap
  have hR : 16 * (R s₁ + 1) ≤ 240 := by rcases hp₁.rounds with h | h | h <;> omega
  have hrdi : s.gpr .rdi = W s₁ := h.1.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hrsi : s.gpr .rsi = s₁.gpr .rsi := h.1.keep _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hr8 : s.gpr .r8 = S s₁ := h.1.r8
  have hW : s.wr = [ivR s₁, dataR s₁, scrR s₁] := by rw [h.1.wr, hp₁.wr]
  have hscr : InRegions s.wr (s.gpr .r8) 2048 := ⟨scrR s₁, by rw [hW]; simp, by
    rw [hr8]; simpa using Offset.contains_base (S s₁) (d := 0) (n := 2048) (k := 2176) (by omega) (by omega)⟩
  have hsch : (⟨s.gpr .rdi, 240⟩ : Region) ∈ s.rd ++ s.wr :=
    List.mem_append_left _ (by rw [h.1.rd, hp₁.rd, hrdi]; simp)
  have hsep : Region.Disjoint ⟨s.gpr .rdi, 240⟩ ⟨s.gpr .r8, 2048⟩ := by
    rw [hrdi, hr8]; exact hp₁.sch_scr.sub_right (Region.sub_prefix (by decide))
  have hK : Keys (R s₁) (wK s₁) s :=
    Aes.X86_64.AesNi.Ecb.keys_congr (keys_entry hp₁) hrdi h.1.rd h.1.wr
      (AesCbc.X86_64.bytesAt_frame h.1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp₁.sch_scr.sub_left (Region.sub_prefix hR)) (by omega))
  refine WP.mono (imcKeys_ok hp₁.rounds (by rw [hrsi, rsi_ofNat]) hscr hsch hsep)
    fun s' ⟨S', hI, hS⟩ => ?_
  have hg := hI.gpr
  have fS : Frame [scrR s₁] s.mem s'.mem := hI.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₁, by simp, by rw [hr8]; exact Region.sub_prefix (by decide)⟩
  refine ⟨⟨⟨by rw [hg, h.1.r8], by rw [hg, h.1.r9], by rw [hg, h.1.r11],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg, h.1.keep r h1 h2 h3 h4 h5 h6 h7],
    by rw [hI.rd, h.1.rd], by rw [hI.wr, h.1.wr], h.1.frame.trans fS, fun j hj => ?_,
    by rw [hg, h.1.rdx], by rw [hg]; exact h.1.tw, ?_⟩, by rw [hg, h.2]⟩,
    dKeys_of_imc hK hscr hsep hI hS, by rw [hg, hrdi], by rw [hg, hrsi], by rw [hg, hr8],
    by rw [hg, h.2, hrdi]⟩
  · rw [AesCbc.X86_64.bytesAt_frame hI.lo (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hr8]
        exact Offset.disjoint_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega))
      (by decide), h.1.buf j hj]
  · rw [hI.lo.readW (r := ⟨dAddr s₁, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hr8]
        exact Offset.disjoint_base _ (by simp only [dOff]; omega) (by simp only [dOff]; omega))
      (by decide), h.1.dl]

theorem encryptVaes_wp {s₀ : State} (h0 : (To.xtsToX86_64 true).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesTo.encryptVaes s₀ fun s' =>
      gprPreserved s₀ s' ∧ (To.xtsToX86_64 true).post s₀ s' := by
  refine crypt_wp (KP := KPe) h0 (fun s₁ hp₁ => kpe_stable hp₁)
    (fun s₁ hp₁ => loop8_ok hp₁ (kpe_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => WP.block_nil ⟨h, kpe_pre hp₁ h⟩)
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact Aes.X86_64.Vaes.aes_ok regs4 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aes_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

theorem decryptVaes_wp {s₀ : State} (h0 : (To.xtsToX86_64 false).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesTo.decryptVaes s₀ fun s' =>
      gprPreserved s₀ s' ∧ (To.xtsToX86_64 false).post s₀ s' := by
  refine crypt_wp (KP := KPd) h0 (fun s₁ hp₁ => kpd_stable hp₁)
    (fun s₁ hp₁ => loop8_ok hp₁ (kpd_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => imc_pre hp₁ h)
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.VaesBlocks.aesDec_ok regs4 (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aesDec_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

end VG.Proof.AesXts.X86_64.VaesTo

/-! ## One-pass XTS-AES with AES-NI on x86-64, out of place: eight blocks at a time

`groupNi_wp` and `loop8Ni_ok`: `OnePassNi.group_wp` and `OnePassNi.loop8_ok`
of `Proof/AesXts/X86_64/AesNi/Loop.lean`, for the out-of-place loop, which
loads each block from `src` (`tPreListTo_ok`); with `crypt_wp`,
`encryptAesNi_wp` and `decryptAesNi_wp`.
-/

namespace VG.Proof.AesXts.X86_64.VaesTo

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesXts.X86_64AesNi (stepT steps constK)
open VG.Impl.AesXts.X86_64VaesTo (groupNi loop8Ni)
open VG.Impl.AesXts.X86_64Vaes (bufOff tPost)
open VG.Impl.Aes.X86_64.AesNi (regs8)
open VG.Proof.AesXts (b16 next_b8)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast XFrame)
open VG.Proof.AesXts.X86_64.Vaes (slot bufR stF xts_word bytesAt_b16 next_add stepW tPostList_ok KPe KPd rsi_ofNat)
open VG.Proof.AesXts.X86_64.OnePassNi (BlkN stepsN_ok)

/-- In the loop: the tweaks of the group at `rax`, and `0x87` in `xmm11`. -/
structure NInv (enc : Bool) (KP : State → Prop) (s₀ : State) (c : Nat) (s : State) : Prop where
  g : GInv enc KP s₀ c c s
  rax : s.gpr .rax = slot s₀ 0
  k87 : qword (s.xmm .xmm11) 0 = 0x87

/-- One group of eight blocks. -/
theorem groupNi_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : BlkN enc f KP s₀) {c : Nat} (hc : c + 8 ≤ N s₀) {s : State}
    (h : NInv enc KP s₀ c s) :
    WP isa (groupNi f) s fun s' => NInv enc KP s₀ (c + 8) s' ∧ s'.cf = some (decide (N s₀ - (c + 8) < 8)) := by
  have hg := h.g
  have hw := hp.data_wrap
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  have inD : ∀ k < 8, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [hg.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  have inT : ∀ k < 8, InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨scrR s₀, by rw [hW]; simp, ?_⟩
    rw [h.rax, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
  -- The tweaks XORed in.
  have hnl := hp.n_lt
  refine WP.seq (WP.mono (tPreListTo_ok regs8 0 s (by decide)
    (fun k hk => hp.ix_in hg.r11 hg.rcx hg.rd (by have : regs8.length = 8 := rfl; omega) (by omega))
    (fun k hk => inRegions_wr (inT k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ hg.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  -- The tweaks XORed in again, and the blocks stored.
  rw [List.append_assoc, WP.block_append_iff]
  have hr11N : (s.gpr .r11).toNat = (Dp s₀).toNat + 16 * c := by rw [hg.r11]; exact hp.blk_toNat (by omega)
  refine WP.mono (tPostList_ok regs8 0 s₂ (by decide) (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (fun k hk => by rw [rd₂, wr₂, g₂]; exact inRegions_wr (inT k hk)) (by rw [g₂, hr11N]; show _ + 16 * (0 + 8) ≤ _; omega)
    (fun k hk => by
      rw [g₂, h.rax, hg.r11, Nat.mul_zero, BitVec.add_zero, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right
        (UPre.scr_sub (by simp only [bufOff]; have : regs8.length = 8 := rfl; omega))).symm))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, hg.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 16 * regs8.length = 128 from rfl] at f₃
  rw [g₂, m₂] at e₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩)
  have hK₃ : qword (s₃.xmm .xmm11) 0 = 0x87 := by
    rw [x₃ _ (by decide), f₂.xmm _ (by decide), x₁ _ (by decide)]; exact h.k87
  -- The tweaks times `α⁸`.
  rw [WP.block_append_iff]
  refine WP.mono (stepsN_ok s₃ hK₃ (fun k hk => by rw [wr₃, wr₂, g₃']; simpa using inT k hk)
      (by rw [g₃', h.rax, slot]; simp only [bufOff]; rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega)
      8 (Nat.le_refl _)) fun s₄ ⟨e₄, f₄, g₄, rd₄, wr₄, x₄⟩ => ?_
  rw [g₃', h.rax] at e₄ f₄
  have g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  have hTb : Region.Sub ⟨slot s₀ 0, 128⟩ (bufR s₀) := by
    rw [slot, Nat.mul_zero, Nat.add_zero]; exact Region.sub_prefix (by decide)
  have kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) rd₄ wr₄ (f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, hTb⟩)
  have hK₄ : qword (s₄.xmm .xmm11) 0 = 0x87 := by rw [x₄ _ (by decide) (by decide)]; exact hK₃
  -- The memory after the group.
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem :=
    hg.frame.trans ((f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data_n hc⟩).trans
      (f₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => buf_scr _ (hTb _ h)⟩))
  have slotE : ∀ j, slot s₀ j = slot s₀ 0 + BitVec.ofNat 64 (16 * j) := fun j => by
    rw [slot, slot, Nat.mul_zero, Nat.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 8 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [AesCbc.X86_64.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (fun _ h => buf_scr _ (hTb _ h))) (by decide)]
    by_cases hin : c ≤ k ∧ k < c + 8
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega⟩
      have hi : i < regs8.length := by have : regs8.length = 8 := rfl; omega
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [hg.r11, blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      have sl : slot s₀ i = s.gpr .rax + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [h.rax, slotE, Nat.zero_add]
      rw [bytesAt_b16, ab, e₃ _ hi, ← sl, ← ab]
      have e1 := e₁ _ hi
      rw [ix_sblk hg.r11 hg.rcx _ i (by omega), hp.src_kept hg.frame (by omega), ← sl] at e1
      have hc' : st (s₂.xmm regs8[i]) = stF enc (R s₀) (wK s₀)
          (st (s₀.mem.readW (sblk s₀ (c + i)) 128 ^^^ s.mem.readW (slot s₀ i) 128)) :=
        (e₂ _ (List.getElem_mem hi)).trans (congrArg (fun v => stF enc (R s₀) (wK s₀) (st v)) e1)
      refine (xts_word enc (R s₀) (wK s₀) _ _ _ hc').trans ?_
      rw [← bytesAt_b16, ← bytesAt_b16, hg.buf i (by omega)]
      simp only [show c + i < c + 8 by omega, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide), hg.data k hk]
      by_cases hlt' : k < c
      · simp only [hlt', ite_true, show k < c + 8 by omega]
      · simp only [hlt', ite_false, show ¬ k < c + 8 by omega]
  have hbuf : ∀ j < 8, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (c + 8 + j) := by
    intro j hj
    rw [bytesAt_b16, slotE, e₄ j hj]
    simp only [hj, ite_true]
    rw [← slotE, f₃.readW (r := ⟨slot s₀ j, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data_n hc)).sub_right (slot_scr (j := j) (by omega))).symm) (by decide)]
    rw [stepW, ← next_b8, ← bytesAt_b16, hg.buf j hj, ← next_add]
    congr 1; omega
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, hg.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, hg.wr]
  -- `add r11, 128`, `sub r9, 8` and `cmp r9, 8`.
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', hg.r11]
  have hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', hg.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hadd : blk s₀ c + 128 = blk s₀ (c + 8) := by
    rw [blk, blk, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 128 = 16 * (c + 8) by omega]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', hg.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', hg.r10], by simp [g₄', hg.rcx],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', hg.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, fun j hj => by rw [hbuf j hj], by simp [g₄', hg.rdx]⟩,
    by simp [g₄', h.rax], by simpa using hK₄⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 8) < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The eight-block loop meets `LoopOk`. -/
theorem loop8Ni_ok {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : BlkN enc f KP s₀) : LoopOk enc (loop8Ni f) KP s₀ := by
  intro s h hcf
  refine WP.ite (decide (N s₀ < 8)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨0, by simpa using hb, h⟩
  · simp at hb
    have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
    have hr8 := h.r8
    have st₁ : WP isa (.block (constK ++ ([.mov .rax (.reg .r8), .alu .add .rax (.imm 256)] : List Instr))) s
        (NInv enc KP s₀ 0) := by
      apply WP.of_runBlock
      simp only [constK, List.cons_append, List.nil_append, ↓reduceIte, runBlock_cons, runStep_some,
        runBlock_nil, exec, readSrc, execAlu, VOp.exec, arithFlags, State.setFlags, State.setReg, e256,
        Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
      refine ⟨h.congr hst (fun r h1 => by simp [h1]) (by simp [State.setV]) (by simp [State.setV])
        (by simp [State.setV]), ?_, ?_⟩
      · simp [State.setV, hr8, slot, bufOff]
      · simp [State.setV, qword]
    refine WP.seq (WP.mono st₁ fun s₁ h₁ => ?_)
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ NInv enc KP s₀ c t
    have hstep : ∀ m t, I m t → WP isa (groupNi f) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI⟩
      refine WP.mono (groupNi_wp hp hst hf hc hI) fun t' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 8) < 8
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'.g⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (N s₀) s₁ ⟨0, by simp, by omega, h₁⟩

theorem encryptAesNi_wp {s₀ : State} (h0 : (To.xtsToX86_64 true).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesTo.encryptAesNi s₀ fun s' =>
      gprPreserved s₀ s' ∧ (To.xtsToX86_64 true).post s₀ s' := by
  refine crypt_wp (KP := KPe) h0 (fun s₁ hp₁ => kpe_stable hp₁)
    (fun s₁ hp₁ => loop8Ni_ok hp₁ (kpe_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => WP.block_nil ⟨h, kpe_pre hp₁ h⟩)
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact Aes.X86_64.AesNi.aes_ok regs8 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aes_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

theorem decryptAesNi_wp {s₀ : State} (h0 : (To.xtsToX86_64 false).pre s₀) :
    WP isa Impl.AesXts.X86_64VaesTo.decryptAesNi s₀ fun s' =>
      gprPreserved s₀ s' ∧ (To.xtsToX86_64 false).post s₀ s' := by
  refine crypt_wp (KP := KPd) h0 (fun s₁ hp₁ => kpd_stable hp₁)
    (fun s₁ hp₁ => loop8Ni_ok hp₁ (kpd_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => imc_pre hp₁ h)
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.AesNi.aesDec_ok regs8 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aesDec_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

end VG.Proof.AesXts.X86_64.VaesTo
