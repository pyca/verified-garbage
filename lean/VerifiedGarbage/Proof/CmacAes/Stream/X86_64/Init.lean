module

import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
public import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
meta import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
meta import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_init`

The code saves `rbx`, `rbp` and `r12` in the scratch buffer, expands the key
into the state, derives the subkeys after the schedule, zeroes the chaining
value and restores the registers: the state then represents the empty message.
The code between the calls is constant time by the taint analysis, and the
calls by their own proofs (`ek_rel`, `sub_rel`), their arguments pinned by
`IMid₁` and `IMid₂`.

The proof is over the part `Z` of the scratch buffer the code may write and
the part `X` of it its calls write (`ICall`): all of it, with any
implementation of AES (`ICall.base`), or, over one that needs no working
space, only the 152 bytes from `vg_cmac_aes_subkeys`'s counter block, at
`scratch + 2048`, to the end of our saved registers (`ICall.free`), which
`initF`, given `scratch - 2048`, writes (`initF_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes sub_of_contains)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes,
the scratch buffer `S`, and the part `Z` of it the code may write: all of it
(`initX86_64`), or only the 152 bytes at `S + 2048` (`initF_wp`). -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) (Z : Region) : Prop where
  rdi : s₀.gpr .rdi = St
  rsi : s₀.gpr .rsi = Kp
  rdx : (s₀.gpr .rdx).toNat = KL
  rcx : s₀.gpr .rcx = S
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, Z]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint Z
  k_s : (⟨Kp, KL⟩ : Region).Disjoint Z
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Kp, KL⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint Z
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_k : (below (s₀.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint Z
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wZ : Z.base.toNat + Z.len ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  /-- The 152 bytes at `S + 2048` are in `Z`. -/
  zIn : ∀ {d n : Nat}, 2048 ≤ d → d + n ≤ 2200 → Z.Contains (S + BitVec.ofNat 64 d) n
  zWrap : (S + BitVec.ofNat 64 2048).toNat + 152 ≤ 2 ^ 64

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) :
    IPre s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx) (s₀.gpr .rdx).toNat ⟨s₀.gpr .rcx, 2304⟩ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p,
    fun _ h₂ => Offset.contains_base _ (by omega) (by omega),
    by rw [toNat_add_lt _ o (by decide)]; omega⟩

theorem IPre.zSub {s₀ : State} {St Kp S : Addr} {KL : Nat} {Z : Region} (hp : IPre s₀ St Kp S KL Z) {d n : Nat}
    (h₁ : 2048 ≤ d) (h₂ : d + n ≤ 2200) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ Z :=
  sub_of_contains (hp.zIn h₁ h₂)

theorem IPre.inZ {s₀ : State} {St Kp S : Addr} {KL : Nat} {Z : Region} (hp : IPre s₀ St Kp S KL Z) {d n : Nat}
    (h₁ : 2048 ≤ d) (h₂ : d + n ≤ 2200) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨Z, by simp, hp.zIn h₁ h₂⟩

/-- The rounds, as `shr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.signExtend 64 (6 : BitVec 32) = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- The memory after saving the registers. -/
def initSavedMem (s : State) (S : Addr) : Mem :=
  ((s.mem.writeW (S + BitVec.ofNat 64 2176) (s.gpr .rbx)).writeW (S + BitVec.ofNat 64 2184) (s.gpr .rbp)).writeW
    (S + BitVec.ofNat 64 2192) (s.gpr .r12)

theorem initSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 24⟩] s.mem (initSavedMem s S) := by
  have c (d : Nat) (hd : d + 8 ≤ 24) : (⟨S + BitVec.ofNat 64 2176, 24⟩ : Region).Contains
      (S + BitVec.ofNat 64 (2176 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ hd (by omega_arith)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _ (c 16 (by decide))

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {St Kp S : Addr} {KL : Nat} {Z : Region} (hp : IPre s₀ St Kp S KL Z) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 KL ∧
      s₁.gpr .rdx = St ∧ s₁.gpr .rcx = S ∧ s₁.gpr .rbx = St ∧ s₁.gpr .rbp = S ∧
      s₁.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = initSavedMem s₀ S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2200) (hd' : 2048 ≤ d) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 :=
    hp.inZ hd' hd
  have hKL : s₀.gpr .rdx = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rdx, toNat_ofNat (by rcases hp.klen with h | h | h <;> omega_arith)])
  refine ⟨_, by
    simp (config := {decide := true}) only [initPre, initSaved, sOff, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, execShift,
      State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hp.rcx, inS 2176 (by decide) (by decide),
      inS 2184 (by decide) (by decide), inS 2192 (by decide) (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, ite_true, ite_false, hp.rdi, hp.rsi, hp.rcx, hKL, rounds_bv hp.klen, Nat.reduceAdd]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r h₁ h₂ h₃ hr => ?_, rfl, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem initSaved_read (s : State) (S : Addr) :
    (initSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .rbx ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .rbp ∧
      (initSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .r12 := by
  have sp (a b : Nat) (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 2304) (hb : b + 8 ≤ 2304) :
      Mem.Sep (S + BitVec.ofNat 64 a) (64 / 8) (S + BitVec.ofNat 64 b) (64 / 8) :=
    Offset.sep S h (by omega_arith) (by omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · rw [initSavedMem, Mem.readW_writeW_sep (sp 2176 2192 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (sp 2176 2184 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [initSavedMem, Mem.readW_writeW_sep (sp 2184 2192 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
  · rw [initSavedMem, Mem.readW_writeW_self64]

/-! ## Between the calls, and after them -/

theorem initMid_ok {s : State} {St S : Addr} {R : Nat} (hb : s.gpr .rbx = St) (hp : s.gpr .rbp = S)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid s = some s' ∧ s'.gpr .rdi = St ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = St + BitVec.ofNat 64 240 ∧ s'.gpr .rcx = S ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, and_self, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, hb, hp, h12, sx240]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem :=
  (m.writeW (St + BitVec.ofNat 64 272) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (St + BitVec.ofNat 64 280) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zeroCv_eq (m : Mem) (St : Addr) : zeroCv m St = zero2 m (St + BitVec.ofNat 64 272) := by
  rw [zeroCv, zero2, Offset.add_add]

theorem initPost_ok {s : State} {St S : Addr} (hb : s.gpr .rbx = St) (hp : s.gpr .rbp = S)
    (w₁ : InRegions s.wr (St + BitVec.ofNat 64 272) 8) (w₂ : InRegions s.wr (St + BitVec.ofNat 64 280) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2176) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2184) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2192) 8) :
    ∃ s', runBlock isa initPost s = some s' ∧
      s'.gpr .rbx = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .rbp = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .r12 = (zeroCv s.mem St).readW (S + BitVec.ofNat 64 2192) 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s'.gpr r = s.gpr r) ∧
      s'.mem = zeroCv s.mem St := by
  refine ⟨_, by
    simp (config := {decide := true}) only [initPost, sOff, runBlock_cons, runStep_some, runBlock_nil,
      at_, exec, readSrc, readSrc32, State.load64, State.store64, State.ea, State.setReg32, offset_nat,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true,
      ite_false, hb, hp, w₁, w₂, r₁, r₂, r₃, Nat.reduceAdd]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, mem_setReg, ite_true, ite_false]
  refine ⟨rfl, rfl, rfl, fun r h₁ h₂ h₃ hr => ?_, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## The whole function -/

theorem IPre.rounds {s₀ : State} {St Kp S : Addr} {KL : Nat} {Z : Region} (hp : IPre s₀ St Kp S KL Z) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgsF s Kp St KL
  rcx : s.gpr .rcx = S
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  r12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  other : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  mem : s.mem = initSavedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} {Z : Region} (hp : IPre s₀ St Kp S KL Z) :
    WP isa (.block initPre) s₀ (IMid₁ s₀ St Kp S KL) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, rsp₁, o₁, m₁, rd₁, wr₁⟩ := initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, rcx₁, rbx₁, rbp₁, r12₁, rsp₁, o₁, m₁, rd₁, wr₁⟩⟩
  exact
  { rdi := rdi₁, rsi := rsi₁, rdx := rdx₁, klen := hp.klen
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp₁]; exact hp.stk_k
    stkW := by rw [rsp₁]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    reads := by
      rw [rd₁, wr₁, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₁, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩ }

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : SArgsF s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6)
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  keep : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {s₀ s : State} {St Kp S : Addr} {KL : Nat} {Z : Region} (hp : IPre s₀ St Kp S KL Z)
    (hb : s.gpr .rbx = St) (hbp : s.gpr .rbp = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6))
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (IMid₂ s₀ St S KL s.mem) := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, sv, mem, rd, wr⟩ := initMid_ok hb hbp h12
  have hw := hp.wSt
  have rsp' : s'.gpr .rsp = s₀.gpr .rsp := by rw [sv _ (by simp [calleeSaved]), hsp]
  have kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have cZ := hp.zSub (d := 2048) (n := 32) (by decide) (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨?_, by rw [sv _ (by simp [calleeSaved]), hb],
    by rw [sv _ (by simp [calleeSaved]), hbp], rsp', fun r h₁ h₂ h₃ hr => by rw [sv r hr, hk r h₁ h₂ h₃ hr],
    mem, by rw [rd, hrd], by rw [wr, hwr]⟩⟩
  exact
  { rdi := rdi, rsi := rsi, rdx := rdx, rcx := rcx, rounds := hp.rounds
    wk := Offset.base_disjoint St (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right cZ
    ks := (hp.st_s.sub_left kSt).sub_right cZ
    stkW := by rw [rsp']; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp']; exact hp.stk_st.sub_right kSt
    stkS := by rw [rsp']; exact hp.stk_s.sub_right cZ
    wrapK := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapS := by have := hp.zWrap; omega_arith
    reads := by
      rw [rd, wr, hrd, hwr, hp.rd, hp.wr]
      refine Covers.cons (Covers.of_sub fun r hr => ?_) (Covers.cons (Covers.of_sub fun r hr => ?_)
        (Covers.cons (Covers.one ⟨Z, by simp, hp.zIn (by decide) (by decide)⟩) Covers.nil))
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
    writes := by
      rw [wr, hwr, hp.wr]
      refine Covers.cons (Covers.of_sub fun r hr => ?_)
        (Covers.cons (Covers.one ⟨Z, by simp, hp.zIn (by decide) (by decide)⟩) Covers.nil)
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩ }

/-- What `init` needs of its calls, with `e`, `c` and `sfx`, for the
writable part `Z S` of each scratch buffer `S`: from their arguments as the
code before them leaves them, they write no more of the scratch buffer than
`X S`, within `Z S` and apart from the registers saved there; and two calls
with the same arguments leak the same. -/
structure ICall (e : Impl.Aes.X86_64.ExpandKey) (c : Impl.Aes.X86_64.Ctr32) (sfx : String)
    (Z X : Addr → Region) : Prop where
  sub : ∀ S, Region.Sub (X S) (Z S)
  slots : ∀ S, (⟨S + BitVec.ofNat 64 2176, 24⟩ : Region).Disjoint (X S)
  ek : ∀ {s₀ s : State} {St Kp S : Addr} {KL : Nat}, IPre s₀ St Kp S KL (Z S) → IMid₁ s₀ St Kp S KL s →
    WP isa (.call e.name e.code) s (EPostX s Kp St KL (X S))
  ekRel : ∀ {s₀ s₀' : State} {St Kp S : Addr} {KL : Nat} {P : State → State → Prop},
    IPre s₀ St Kp S KL (Z S) → IPre s₀' St Kp S KL (Z S) → s₀.gpr .rsp = s₀'.gpr .rsp →
    (∀ a b, P a b → IMid₁ s₀ St Kp S KL a ∧ IMid₁ s₀' St Kp S KL b) →
    RelCT isa P (.call e.name e.code) fun _ _ => True
  sk : ∀ {s₀ s : State} {St Kp S : Addr} {KL : Nat} {m : Mem}, IPre s₀ St Kp S KL (Z S) →
    IMid₂ s₀ St S KL m s →
    WP isa (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.X86_64.subkeys c)) s
      (SPostX s St (St + BitVec.ofNat 64 240) (KL / 4 + 6) (X S))
  skRel : ∀ {s₀ s₀' : State} {St Kp S : Addr} {KL : Nat} {P : State → State → Prop},
    IPre s₀ St Kp S KL (Z S) → IPre s₀' St Kp S KL (Z S) → s₀.gpr .rsp = s₀'.gpr .rsp →
    (∀ a b, P a b → (∃ m, IMid₂ s₀ St S KL m a) ∧ ∃ m, IMid₂ s₀' St S KL m b) →
    RelCT isa P (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.X86_64.subkeys c)) fun _ _ => True

theorem init_wpG {e : Impl.Aes.X86_64.ExpandKey} {c : Impl.Aes.X86_64.Ctr32} {sfx : String} {Z X : Addr → Region}
    (T : ICall e c sfx Z X) {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL (Z S)) :
    WP isa (init e c sfx) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.Cmac.Repr s'.mem St (Spec.Aes.bytesAt s₀.mem Kp KL) [] := by
  have hw := hp.wSt
  have hR := hp.rounds
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (T.ek hp h₁) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  refine WP.seq (WP.mono (initMid_wp hp (by rw [g₂ _ (by simp [calleeSaved]), h₁.rbx])
    (by rw [g₂ _ (by simp [calleeSaved]), h₁.rbp]) (by rw [g₂ _ (by simp [calleeSaved]), h₁.r12])
    (by rw [g₂ _ (by simp [calleeSaved]), h₁.rsp]) (by rw [h₂.rd, h₁.rd]) (by rw [h₂.wr, h₁.wr])
    (fun r a b c hr => by rw [g₂ r hr, h₁.other r a b c hr])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (T.sk hp h₃) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s₃.gpr r := h₄.saved r hr
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inR (d : Nat) (hd : d + 8 ≤ 2200) (hd' : 2048 ≤ d) :
      InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := hp.inZ hd' hd
    rw [h₄.wr, h₃.wr]; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₅, run₅, rbx₅, rbp₅, r12₅, keep₅, m₅⟩ := initPost_ok (s := s₄) (St := St) (S := S)
    (by rw [g₄ _ (by simp [calleeSaved]), h₃.rbx]) (by rw [g₄ _ (by simp [calleeSaved]), h₃.rbp])
    (inSt 272 (by decide)) (inSt 280 (by decide)) (inR 2176 (by decide) (by decide))
    (inR 2184 (by decide) (by decide)) (inR 2192 (by decide) (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- The memory, step by step.
  have fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem (zeroCv s₄.mem St) := by
    rw [zeroCv_eq]; exact Proof.CmacAes.X86_64.frame_store2 _ _ _
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 24⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact initSavedMem_frame _ _
  have f₂ : Frame [⟨St, 240⟩, X S, below (s₀.gpr .rsp) 16] s₁.mem s₂.mem := by
    rw [← h₁.rsp]; exact h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, X S, below (s₀.gpr .rsp) 16] s₃.mem s₄.mem := by
    rw [← h₃.rsp]; exact h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  have sl := hp.zSub (d := 2176) (n := 24) (by decide) (by decide)
  have xZ := T.sub S
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, X S, below (s₀.gpr .rsp) 16, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2200) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S + BitVec.ofNat 64 2176, 24⟩ :=
      Offset.sub S hd (by omega_arith)
    have subZ : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ (Z S) := fun a h => sl a (sub a h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left subZ
    · exact (T.slots S).sub_left sub
    · exact hp.stk_s.symm.sub_left subZ
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left subZ
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left subZ
  have rd' (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2200) :
      (zeroCv s₄.mem St).readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c := Region.contains_self (S + BitVec.ofNat 64 d) 8
    rw [fz.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]) d hd hd') (by decide),
      f₄.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> simp) d hd hd') (by decide), m₃,
      f₂.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> simp) d hd hd') (by decide)]
  obtain ⟨sv₁, sv₂, sv₃⟩ := initSaved_read s₀ S
  have m₁ := h₁.mem
  -- The state, outside what the last block writes.
  have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
  have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega_arith
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbx₅, rd' 2176 (by decide) (by decide), m₁]; exact sv₁
    · rw [rbp₅, rd' 2184 (by decide) (by decide), m₁]; exact sv₂
    · rw [keep₅ _ (by decide) (by decide) (by decide) (by simp [calleeSaved]),
        g₄ _ (by simp [calleeSaved]), h₃.rsp]
    · rw [r12₅, rd' 2192 (by decide) (by decide), m₁]; exact sv₃
    all_goals rw [keep₅ _ (by decide) (by decide) (by decide) (by simp [calleeSaved]),
      g₄ _ (by simp [calleeSaved]), h₃.keep _ (by decide) (by decide) (by decide) (by simp [calleeSaved])]
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [m₅, fz.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_st.sub_right (Offset.sub_base St (by decide))) (by decide),
      f₄.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st.sub_right (Offset.sub_base St (by decide))
        · exact hp.ret_s.sub_right xZ
        · exact Offset.base_disjoint_below _ (by decide)) (by decide), m₃,
      f₂.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st.sub_right (Region.sub_prefix (by decide))
        · exact hp.ret_s.sub_right xZ
        · exact Offset.base_disjoint_below _ (by decide)) (by decide),
      f₁.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_s.sub_right sl) (by decide)]
  · rw [Proof.Cmac.Stream.repr_iff]
    have hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right sl) (by have := hp.wK; omega_arith)
    have hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [m₅, bytesAt_frame fz (dSt d n (by omega_arith)) (by omega_arith), bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
        · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right xZ
        · exact (hp.stk_st.sub_right (Offset.sub_base St (by omega_arith))).symm) (by omega_arith), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega_arith)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 := by
        rw [m₅]; exact bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅, zeroCv_eq]; exact (zero2_bytes _ _).trans rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key_scratch` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  r12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  keep : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem init_relG {e : Impl.Aes.X86_64.ExpandKey} {c : Impl.Aes.X86_64.Ctr32} {sfx : String} {Z X : Addr → Region}
    (T : ICall e c sfx Z X) {s₀ s₀' : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL (Z S))
    (hp' : IPre s₀' St Kp S KL (Z S)) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init e c sfx) fun _ _ => True := by
  have q2 : s₀.gpr .rdi = s₀'.gpr .rdi := by rw [hp.rdi, hp'.rdi]
  have q3 : s₀.gpr .rsi = s₀'.gpr .rsi := by rw [hp.rsi, hp'.rsi]
  have q4 : s₀.gpr .rdx = s₀'.gpr .rdx := BitVec.eq_of_toNat_eq (by rw [hp.rdx, hp'.rdx])
  have q5 : s₀.gpr .rcx = s₀'.gpr .rcx := by rw [hp.rcx, hp'.rcx]
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .rsp]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := IMid₁ s₀ St Kp S KL) (F₂ := IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩
  have after {t₀ s : State} (hq : IPre t₀ St Kp S KL (Z S)) (h : IMid₁ t₀ St Kp S KL s) :
      WP isa (.call e.name e.code) s (IAfter t₀ St S KL) :=
    WP.mono (T.ek hq h) fun _ h₂ =>
      ⟨by rw [h₂.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₂.saved _ (by simp [calleeSaved]), h.rbp],
        by rw [h₂.saved _ (by simp [calleeSaved]), h.r12], by rw [h₂.saved _ (by simp [calleeSaved]), h.rsp],
        fun r a b c hr => by rw [h₂.saved r hr, h.other r a b c hr], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩
  have ek := (T.ekRel (P := fun a b => IMid₁ s₀ St Kp S KL a ∧ IMid₁ s₀' St Kp S KL b) hp hp' q1
    fun _ _ h => h).wp
    (F₁ := IAfter s₀ St S KL) (F₂ := IAfter s₀' St S KL) fun a b h => ⟨after hp h.1, after hp' h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ St S KL a ∧ IAfter s₀' St S KL b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.rbp, h.2.rbp]
      · rw [h.1.r12, h.2.r12]
      · rw [h.1.rsp, h.2.rsp, q1]) hB).wp
    (F₁ := fun (s : State) => ∃ m, IMid₂ s₀ St S KL m s) (F₂ := fun (s : State) => ∃ m, IMid₂ s₀' St S KL m s)
    fun a b h => ⟨WP.mono (initMid_wp hp h.1.rbx h.1.rbp h.1.r12 h.1.rsp h.1.rd h.1.wr h.1.keep)
        fun _ h => ⟨_, h⟩,
      WP.mono (initMid_wp hp' h.2.rbx h.2.rbp h.2.r12 h.2.rsp h.2.rd h.2.wr h.2.keep) fun _ h => ⟨_, h⟩⟩
  have sk := (T.skRel (P := fun a b => (∃ m, IMid₂ s₀ St S KL m a) ∧ ∃ m, IMid₂ s₀' St S KL m b) hp hp' q1
    fun _ _ h => h).wp
    (F₁ := fun (s : State) => s.gpr .rbx = St ∧ s.gpr .rbp = S)
    (F₂ := fun (s : State) => s.gpr .rbx = St ∧ s.gpr .rbp = S)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨WP.mono (T.sk hp h₁) fun _ h => ⟨by rw [h.saved _ (by simp [calleeSaved]), h₁.rbx],
          by rw [h.saved _ (by simp [calleeSaved]), h₁.rbp]⟩,
        WP.mono (T.sk hp' h₂) fun _ h => ⟨by rw [h.saved _ (by simp [calleeSaved]), h₂.rbx],
          by rw [h.saved _ (by simp [calleeSaved]), h₂.rbp]⟩⟩
  have p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .rbx = St ∧ a.gpr .rbp = S) ∧ b.gpr .rbx = St ∧ b.gpr .rbp = S) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((ek.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

/-! ## The instances -/

/-- Over any implementation of AES, with all of the scratch buffer. -/
theorem ICall.base (v : Ctr32Impl) :
    ICall v.expand v.callee v.suffix (fun S => ⟨S, 2304⟩) (fun S => ⟨S, 2176⟩) := by
  have eargs {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL ⟨S, 2304⟩)
      (h : IMid₁ s₀ St Kp S KL s) : EArgs s Kp St S KL :=
    h.args.full h.rcx (hp.k_s.sub_right (Region.sub_prefix (by decide)))
      ((hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))
      (by rw [h.rsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide)))
      (by
        rw [h.wr, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩)
  have sargs {s₀ s : State} {St Kp S : Addr} {KL : Nat} {m : Mem} (hp : IPre s₀ St Kp S KL ⟨S, 2304⟩)
      (h : IMid₂ s₀ St S KL m s) : SArgs s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6) :=
    h.args.full ((hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))
      ((hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Region.sub_prefix (by decide)))
      (by rw [h.rsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide)))
      (by have := hp.wZ; simp only at this; omega)
      (by
        rw [h.wr, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩)
  exact
  { sub := fun _ => Region.sub_prefix (by decide)
    slots := fun _ => Offset.disjoint_base _ (by decide) (by decide)
    ek := fun hp h => WP.mono (ek_call v (eargs hp h)) fun _ h' => h'.x (Region.sub_prefix (by decide))
    ekRel := fun hp hp' q h => ek_rel v fun a b hab =>
      ⟨_, _, _, _, eargs hp (h a b hab).1, eargs hp' (h a b hab).2, by
        rw [(h a b hab).1.rsp, (h a b hab).2.rsp, q]⟩
    sk := fun hp h => WP.mono (sub_call v _ (sargs hp h)) fun _ h' => h'.x fun _ h => h
    skRel := fun hp hp' q h => sub_rel v _ fun a b hab =>
      ⟨_, _, _, _, sargs hp (h a b hab).1.choose_spec, sargs hp' (h a b hab).2.choose_spec, by
        rw [(h a b hab).1.choose_spec.rsp, (h a b hab).2.choose_spec.rsp, q]⟩ }

/-- Over an implementation of `vg_aes_ctr32` that needs no working space, with
`vg_aes_expand_key_scratch_aesni`, which needs none either: only the 152
bytes at `S + 2048`, of which the calls write the first 32. -/
theorem ICall.free (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ICall ekF v.callee v.suffix (fun S => ⟨S + BitVec.ofNat 64 2048, 152⟩)
      (fun S => ⟨S + BitVec.ofNat 64 2048, 32⟩) where
  sub S := Offset.sub S (by decide) (by decide)
  slots S := Offset.disjoint S (by decide) (by decide) (by decide)
  ek _ h := ek_callF h.args
  ekRel _ _ q h := ek_relF fun a b hab =>
    ⟨_, _, _, (h a b hab).1.args, (h a b hab).2.args, by rw [(h a b hab).1.rsp, (h a b hab).2.rsp, q]⟩
  sk _ h := sub_callF v f _ h.args
  skRel _ _ q h := sub_relF v f _ fun a b hab =>
    ⟨_, _, _, _, (h a b hab).1.choose_spec.args, (h a b hab).2.choose_spec.args, by
      rw [(h a b hab).1.choose_spec.rsp, (h a b hab).2.choose_spec.rsp, q]⟩

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' :=
  init_wpG (ICall.base v) (IPre.of h0)

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initX86_64.pre initX86_64.pub (init v.expand v.callee v.suffix) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp' : IPre s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx) (s₀.gpr .rdx).toNat ⟨s₀.gpr .rcx, 2304⟩ := by
    rw [q2, q3, q4, q5]; exact IPre.of h₂
  exact (init_relG (ICall.base v) (IPre.of h₁) hp' q1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Without working space for the functions called -/

/-- `initX86_64` with a scratch buffer of 152 bytes, for `initF`. -/
def initX86_64F : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let key : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scr : Region := ⟨s.gpr .rcx, 152⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint key ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint key ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 152 ≤ 2 ^ 64 ∧
      ((s.gpr .rdx).toNat = 16 ∨ (s.gpr .rdx).toNat = 24 ∨ (s.gpr .rdx).toNat = 32)
  post := initX86_64.post
  pub := initX86_64.pub

/-- The `sub` before `init`. -/
theorem subF_ok (s₀ : State) :
    ∃ s₁, runBlock isa [.alu .sub .rcx (.imm (BitVec.ofNat 32 2048))] s₀ = some s₁ ∧
      s₁.gpr .rcx = s₀.gpr .rcx - BitVec.ofNat 64 2048 ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  refine ⟨_, by simp only [runBlock_cons, exec, readSrc, execAlu]; rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ↓reduceIte]
  exact ⟨by rw [show BitVec.signExtend 64 (BitVec.ofNat 32 2048) = BitVec.ofNat 64 2048 by decide],
    fun r h => by simp [h], trivial, trivial, trivial⟩

theorem IPre.ofF {s₀ s₁ : State} (h : initX86_64F.pre s₀)
    (rcx : s₁.gpr .rcx = s₀.gpr .rcx - BitVec.ofNat 64 2048) (g : ∀ r, r ≠ .rcx → s₁.gpr r = s₀.gpr r)
    (rd : s₁.rd = s₀.rd) (wr : s₁.wr = s₀.wr) :
    IPre s₁ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx - BitVec.ofNat 64 2048) (s₀.gpr .rdx).toNat
      ⟨s₀.gpr .rcx - BitVec.ofNat 64 2048 + BitVec.ofNat 64 2048, 152⟩ := by
  obtain ⟨a, b, c, d, e, f, g', h, i, j, k, l, m, n, o, p⟩ := h
  have e0 : s₀.gpr .rcx - BitVec.ofNat 64 2048 + BitVec.ofNat 64 2048 = s₀.gpr .rcx := BitVec.sub_add_cancel _ _
  have sp := g .rsp (by decide)
  rw [e0]
  refine ⟨g _ (by decide), g _ (by decide), by rw [g _ (by decide)], rcx, by rw [sp]; exact a,
    by rw [rd]; exact b, by rw [wr]; exact c, d, e, f, by rw [sp]; exact g', by rw [sp]; exact h,
    by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l, m, n, o, p,
    fun h₁ h₂ => ?_, by rw [e0]; exact o⟩
  rw [sub_add_ofNat _ h₁]; exact Offset.contains_base _ (by omega) (by omega)

theorem initF_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ : State} (h0 : initX86_64F.pre s₀) :
    WP isa (initF ekF v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64F.post s₀ s' := by
  obtain ⟨s₁, run₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := subF_ok s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := IPre.ofF h0 rcx₁ g₁ rd₁ wr₁
  refine WP.mono (init_wpG (ICall.free v f) hp) fun s' ⟨⟨hs, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hs r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · rw [m₁] at hpost; exact hpost

/-- What the `sub` before `init` leaves. -/
def SubF (s₀ s : State) : Prop :=
  s.gpr .rcx = s₀.gpr .rcx - BitVec.ofNat 64 2048 ∧ (∀ r, r ≠ .rcx → s.gpr r = s₀.gpr r) ∧
    s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

theorem initF_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ConstantTime isa initX86_64F.pre initX86_64F.pub (initF ekF v.callee v.suffix) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (.block [.alu .sub .rcx (.imm (BitVec.ofNat 32 2048))]) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SubF s₀) (F₂ := SubF s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, r, h⟩ := subF_ok a
      obtain ⟨_, r', h'⟩ := subF_ok b
      exact ⟨WP.of_runBlock ⟨_, r, h⟩, WP.of_runBlock ⟨_, r', h'⟩⟩
  have r : RelCT isa (fun a b => SubF s₀ a ∧ SubF s₀' b) (init ekF v.callee v.suffix) fun _ _ => True := by
    intro x y t t' x' y' ⟨⟨rcx₁, g₁, _, rd₁, wr₁⟩, ⟨rcx₂, g₂, _, rd₂, wr₂⟩⟩ ex ey
    have hp := IPre.ofF h₁ rcx₁ g₁ rd₁ wr₁
    have hp' := IPre.ofF h₂ rcx₂ g₂ rd₂ wr₂
    rw [← q2, ← q3, ← q4, ← q5] at hp'
    exact init_relG (ICall.free v f) hp hp' (by rw [g₁ _ (by decide), g₂ _ (by decide), q1])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact ((a.mono (fun _ _ h => h) fun _ _ h => h.2).seq r _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64
