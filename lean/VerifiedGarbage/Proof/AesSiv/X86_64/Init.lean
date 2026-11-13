module

import VerifiedGarbage.Proof.AesSiv.X86_64.Common
public import VerifiedGarbage.Proof.AesSiv.X86_64.Contract
public import VerifiedGarbage.Impl.AesSiv.X86_64
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Common
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Contract
meta import VerifiedGarbage.Impl.AesSiv.X86_64
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
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
# AES-SIV on x86-64: `vg_aes_siv_init`

The code saves `rbx`, `rbp` and `r12`–`r14` in the working space, expands
`K1` into the context, derives its subkeys after the schedule, expands `K2`
after them and restores the registers: the context is then that of the key
(`Spec.Siv.KeyRepr`). The code between the calls is constant time by the
taint analysis, and the calls by their own proofs (`ek_rel`, `sub_rel`).

The proof is over the part `Z` of the working space the code may write, the
part `X` of it its calls write, and where `vg_cmac_aes_subkeys`'s scratch
buffer is (`x`, `ICall`): all of it, with any implementation of AES
(`ICall.base`), or, over one that needs no working space, only the 72 bytes
of our saved registers and `vg_cmac_aes_subkeys`'s counter block and saved
registers after them (`ICall.free`), which `initF`, given
`scratch - saveOff`, writes (`initF_wp`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.CmacAes.Stream.X86_64 (EArgs EPost SArgs SPost ek_call sub_call ek_rel sub_rel toNat_ofNat
  toNat_add_lt EArgsF EPostX SArgsF SPostX ekF ek_callF ek_relF sub_callF sub_relF sub_add_ofNat)
open VG.Proof.CmacAes.X86_64 (sub_of_contains)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the key `Kp` of `KL` bytes, the context `Ct`,
the working space `S`, the part `Z` of it the code may write, and
`vg_cmac_aes_subkeys`'s scratch buffer at `x` from `S`: all of it, at
`csOff` (`initX86_64`), or the 72 bytes at `S + saveOff`, with that scratch
buffer's counter block and saved registers after ours (`initF_wp`). -/
structure IPre (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (x : BitVec 32) (Z : Region) : Prop where
  rdi : s₀.gpr .rdi = Kp
  rsi : (s₀.gpr .rsi).toNat = KL
  rdx : s₀.gpr .rdx = Ct
  rcx : s₀.gpr .rcx = S
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨Ct, 512⟩, Z]
  k_c : (⟨Kp, KL⟩ : Region).Disjoint ⟨Ct, 512⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint Z
  c_s : (⟨Ct, 512⟩ : Region).Disjoint Z
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Kp, KL⟩
  ret_c : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Ct, 512⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint Z
  stk_k : (below (s₀.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stk_c : (below (s₀.gpr .rsp) 16).Disjoint ⟨Ct, 512⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint Z
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wC : Ct.toNat + 512 ≤ 2 ^ 64
  wZ : Z.base.toNat + Z.len ≤ 2 ^ 64
  klen : KL = 32 ∨ KL = 48 ∨ KL = 64
  /-- Our saved registers are in `Z`. -/
  sIn : ∀ {d n : Nat}, 160 ≤ d → d + n ≤ 200 → Z.Contains (S + BitVec.ofNat 64 d) n
  /-- … and so are `vg_cmac_aes_subkeys`'s counter block and saved registers. -/
  cIn : ∀ {d n : Nat}, 2048 ≤ d → d + n ≤ 2080 →
    Z.Contains (S + BitVec.signExtend 64 x + BitVec.ofNat 64 d) n
  cWrap : (S + BitVec.signExtend 64 x + BitVec.ofNat 64 2048).toNat + 32 ≤ 2 ^ 64

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) :
    IPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat (BitVec.ofNat 32 csOff)
      ⟨s₀.gpr .rcx, 2560⟩ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p,
    fun _ h₂ => Offset.contains_base _ (by omega) (by omega),
    fun _ h₂ => by
      rw [csOff, sx_ofNat (by decide), Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega),
    by rw [csOff, sx_ofNat (by decide), Offset.add_add, toNat_add_lt _ o (by decide)]; omega⟩

theorem half_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 1 = BitVec.ofNat 64 (KL / 2) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_bv {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 64 KL >>> 3 + BitVec.signExtend 64 (BitVec.ofNat 32 6) = BitVec.ofNat 64 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem IPre.rounds {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region} (hp : IPre s₀ Kp Ct S KL x Z) :
    KL / 8 + 6 = 10 ∨ KL / 8 + 6 = 12 ∨ KL / 8 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

theorem IPre.half {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region} (hp : IPre s₀ Kp Ct S KL x Z) :
    KL / 2 = 16 ∨ KL / 2 = 24 ∨ KL / 2 = 32 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 (KL / 2) ∧
      s₁.gpr .rdx = Ct ∧ s₁.gpr .rcx = S + BitVec.ofNat 64 256 ∧ s₁.gpr .rbx = Kp ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (KL / 2) ∧ s₁.gpr .r12 = Ct ∧ s₁.gpr .r13 = S ∧
      s₁.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6) ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
      (∀ r ∈ calleeSaved, r ∉ initSaved.map Prod.fst → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = Spill.saveMem s₀.mem S s₀.gpr initSaved ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : 160 ≤ d) (hd' : d + 8 ≤ 200) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨Z, by simp, hp.sIn hd hd'⟩
  have hKL : s₀.gpr .rsi = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rsi, toNat_ofNat (by rcases hp.klen with h | h | h <;> omega_arith)])
  have hrun := Spill.save_run .rcx initSaved s₀ (fun p hp' => by
    simp only [initSaved, saveOff, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [hp.rcx]
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;> exact inS _ (by decide) (by decide))
  refine ⟨_, by
    rw [initPre, show saveCode .rcx initSaved = Spill.saveCode .rcx initSaved from rfl, runBlock_append,
      hrun, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, runBlock_cons, runStep_some, exec, readSrc,
      execShift, imm, csOff, Option.map_some, gpr_setReg, 
      ]
    rfl, ?_⟩
  simp (config := {decide := true}) only [↓reduceIte, Nat.reduceSub, Nat.reducePow, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, hp.rdi, hp.rdx, hp.rcx, hKL, half_bv hp.klen, rounds_bv hp.klen,
    sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r hr hn => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [initSaved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- The arguments of a call of `vg_aes_expand_key_scratch` on half the key,
from offset `a` (0 or `KL / 2`), into the context at offset `c`, as the code
leaves them: with the working space of the functions called at `S + csOff`. -/
structure EArgsS (s₀ : State) (Kp Ct S : Addr) (KL a c : Nat) (s : State) : Prop where
  args : EArgsF s (Kp + BitVec.ofNat 64 a) (Ct + BitVec.ofNat 64 c) (KL / 2)
  rcx : s.gpr .rcx = S + BitVec.ofNat 64 256
  ha : a + KL / 2 ≤ KL
  hc : c + 240 ≤ 512
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  args : EArgsS s₀ Kp Ct S KL 0 0 s
  rbx : s.gpr .rbx = Kp
  rbp : s.gpr .rbp = BitVec.ofNat 64 (KL / 2)
  r12 : s.gpr .r12 = Ct
  r13 : s.gpr .r13 = S
  r14 : s.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  other : ∀ r ∈ calleeSaved, r ∉ initSaved.map Prod.fst → s.gpr r = s₀.gpr r
  mem : s.mem = Spill.saveMem s₀.mem S s₀.gpr initSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IPre.sC {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (_hp : IPre s₀ Kp Ct S KL x Z) {d n : Nat}
    (h : d + n ≤ 512) : Region.Sub ⟨Ct + BitVec.ofNat 64 d, n⟩ ⟨Ct, 512⟩ :=
  Offset.sub_base Ct (by omega_arith)

theorem IPre.sK {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (_hp : IPre s₀ Kp Ct S KL x Z) {d n : Nat}
    (h : d + n ≤ KL) : Region.Sub ⟨Kp + BitVec.ofNat 64 d, n⟩ ⟨Kp, KL⟩ :=
  Offset.sub_base Kp (by omega_arith)

/-- The counter block and saved registers of `vg_cmac_aes_subkeys`, in `Z`. -/
theorem IPre.cSub {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z) :
    Region.Sub ⟨S + BitVec.signExtend 64 x + BitVec.ofNat 64 2048, 32⟩ Z :=
  sub_of_contains (hp.cIn (by decide) (by decide))

/-- Our saved registers, in `Z`. -/
theorem IPre.slSub {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z) : Region.Sub ⟨S + BitVec.ofNat 64 160, 40⟩ Z :=
  sub_of_contains (hp.sIn (by decide) (by decide))

/-- The arguments of a call of `vg_aes_expand_key_scratch` on half the key, from
offset `a` (0 or `KL / 2`), into the context at offset `c`. -/
theorem IPre.eargs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z) {a c : Nat}
    (ha : a + KL / 2 ≤ KL) (hc : c + 240 ≤ 512)
    (rdi : s.gpr .rdi = Kp + BitVec.ofNat 64 a) (rsi : s.gpr .rsi = BitVec.ofNat 64 (KL / 2))
    (rdx : s.gpr .rdx = Ct + BitVec.ofNat 64 c) (rcx : s.gpr .rcx = S + BitVec.ofNat 64 256)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    EArgsS s₀ Kp Ct S KL a c s where
  args :=
    { rdi := rdi
      rsi := rsi
      rdx := rdx
      klen := hp.half
      kw := (hp.k_c.sub_left (hp.sK ha)).sub_right (hp.sC hc)
      stkK := by rw [rsp]; exact hp.stk_k.sub_right (hp.sK ha)
      stkW := by rw [rsp]; exact hp.stk_c.sub_right (hp.sC hc)
      reads := by
        rw [rd, wr, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, a, rfl, by simp; omega_arith⟩
        · exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega_arith⟩
      writes := by
        rw [wr, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact ⟨⟨Ct, 512⟩, by simp, c, rfl, by simp; omega_arith⟩ }
  rcx := rcx
  ha := ha
  hc := hc
  rsp := rsp
  rd := rd
  wr := wr

theorem initPre_wp {s₀ : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z) : WP isa (.block initPre) s₀ (IMid₁ s₀ Kp Ct S KL) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, rsp₁, o₁, m₁, rd₁, wr₁⟩ :=
    initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨hp.eargs (a := 0) (c := 0) (by omega_arith) (by decide) (by rw [rdi₁, k0])
    rsi₁ (by rw [rdx₁, k0]) rcx₁ rsp₁ rd₁ wr₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, rsp₁, o₁, m₁, rd₁, wr₁⟩⟩

/-! ## Between the calls -/

theorem initMid₁_ok {s : State} {Ct S : Addr} {R : Nat} (x : BitVec 32) (h12 : s.gpr .r12 = Ct)
    (h13 : s.gpr .r13 = S) (h14 : s.gpr .r14 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa (initMid₁At x) s = some s' ∧ s'.gpr .rdi = Ct ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = Ct + BitVec.ofNat 64 240 ∧ s'.gpr .rcx = S + BitVec.signExtend 64 x ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid₁At, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [↓reduceIte, Nat.reducePow, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, h12, h13, h14,
    sx_ofNat (show 240 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem initMid₂_ok {s : State} {Kp Ct S : Addr} {H : Nat} (hb : s.gpr .rbx = Kp)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 H) (h12 : s.gpr .r12 = Ct) (h13 : s.gpr .r13 = S) :
    ∃ s', runBlock isa initMid₂ s = some s' ∧ s'.gpr .rdi = Kp + BitVec.ofNat 64 H ∧
      s'.gpr .rsi = BitVec.ofNat 64 H ∧ s'.gpr .rdx = Ct + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = S + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid₂, imm, csOff, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [↓reduceIte, Nat.reducePow, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, hb, hbp, h12, h13,
    sx_ofNat (show 272 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The arguments of the call of `vg_cmac_aes_subkeys`, as the code leaves them. -/
structure SArgsS (s₀ : State) (Ct S : Addr) (KL : Nat) (x : BitVec 32) (s : State) : Prop where
  args : SArgsF s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.signExtend 64 x) (KL / 8 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The arguments of the call of `vg_cmac_aes_subkeys`. -/
theorem IPre.sargs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z)
    (rdi : s.gpr .rdi = Ct) (rsi : s.gpr .rsi = BitVec.ofNat 64 (KL / 8 + 6))
    (rdx : s.gpr .rdx = Ct + BitVec.ofNat 64 240) (rcx : s.gpr .rcx = S + BitVec.signExtend 64 x)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    SArgsS s₀ Ct S KL x s where
  args :=
    { rdi := rdi
      rsi := rsi
      rdx := rdx
      rcx := rcx
      rounds := hp.rounds
      wk := Offset.base_disjoint Ct (by decide) (by have := hp.wC; omega_arith)
      ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right hp.cSub
      ks := (hp.c_s.sub_left (hp.sC (by decide))).sub_right hp.cSub
      stkW := by rw [rsp]; exact hp.stk_c.sub_right (Region.sub_prefix (by decide))
      stkK := by rw [rsp]; exact hp.stk_c.sub_right (hp.sC (by decide))
      stkS := by rw [rsp]; exact hp.stk_s.sub_right hp.cSub
      wrapK := by rw [toNat_add_lt Ct hp.wC (by decide)]; have := hp.wC; omega_arith
      wrapS := hp.cWrap
      reads := by
        rw [rd, wr, hp.rd, hp.wr]
        refine Covers.cons (Covers.of_sub fun r hr => ?_) (Covers.cons (Covers.of_sub fun r hr => ?_)
          (Covers.cons (Covers.one ⟨Z, by simp, hp.cIn (by decide) (by decide)⟩) Covers.nil))
        · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨Ct, 512⟩, by simp, 0, by simp, by simp⟩
        · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩
      writes := by
        rw [wr, hp.wr]
        refine Covers.cons (Covers.of_sub fun r hr => ?_)
          (Covers.cons (Covers.one ⟨Z, by simp, hp.cIn (by decide) (by decide)⟩) Covers.nil)
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨Ct, 512⟩, by simp, 240, rfl, by simp⟩ }
  rsp := rsp
  rd := rd
  wr := wr

/-! ## The key context -/

/-- The context `init` leaves is that of the key: the schedule of `K1`, its
subkeys and the schedule of `K2`, each where the calls left it. -/
theorem keyRepr_of {m m₀ : Mem} {Ct Kp : Addr} {KL : Nat} (hl : KL = 32 ∨ KL = 48 ∨ KL = 64)
    (h1 : Spec.Aes.bytesAt m Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2)))
    (hs : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).2)
    (h2 : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 272) (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2))) :
    Spec.Siv.KeyRepr m Ct (Spec.Aes.bytesAt m₀ Kp KL) := by
  have hKL : KL = KL / 2 + KL / 2 := by omega_arith
  have hlen := Proof.Cmac.bytesAt_length m₀ Kp KL
  have e8 : KL / 8 = KL / 2 / 4 := by omega_arith
  have k1 : (Spec.Aes.bytesAt m₀ Kp KL).take (KL / 2) = Spec.Aes.bytesAt m₀ Kp (KL / 2) := by
    have := take_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have k2 : (Spec.Aes.bytesAt m₀ Kp KL).drop (KL / 2) =
      Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2) := by
    have := drop_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have hs' : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      Spec.Aes.bytesAt m (Ct + 240) 16 ++ Spec.Aes.bytesAt m (Ct + 256) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add]; rfl
  have ka : Spec.Cmac.aes (Spec.Aes.bytesAt m₀ Kp (KL / 2)) =
      Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))) := by
    rw [Spec.Cmac.aes, Proof.Cmac.bytesAt_length, Spec.Aes.rounds, e8]
  rw [hs', ← ka] at hs
  obtain ⟨hs1, hs2⟩ := List.append_inj hs (by
    rw [Proof.Cmac.bytesAt_length, Spec.Cmac.aes]; exact (Proof.Cmac.subkeys_aes_length _ _).symm)
  refine ⟨by rw [hlen]; exact hl, ?_, ?_, ?_, ?_⟩
  · rw [hlen, k1, e8]; exact h1
  · rw [hlen, k1]; exact hs1
  · rw [hlen, k1]; exact hs2
  · rw [hlen, k2, e8]; exact h2

/-! ## The whole function -/

/-- What `init` needs of its calls, with `e`, `c` and `sfx`, for the writable
part `Z S` of each working space `S` and `vg_cmac_aes_subkeys`'s scratch
buffer at `x` from it: from their arguments as the code before them leaves
them, they write no more of the working space than `X S`, within `Z S` and
apart from our saved registers; and two calls with the same arguments leak
the same. -/
structure ICall (x : BitVec 32) (e : Impl.Aes.X86_64.ExpandKey) (c : Impl.Aes.X86_64.Ctr32) (sfx : String)
    (Z X : Addr → Region) : Prop where
  sub : ∀ S, Region.Sub (X S) (Z S)
  slots : ∀ S, (⟨S + BitVec.ofNat 64 160, 40⟩ : Region).Disjoint (X S)
  ek : ∀ {s₀ s : State} {Kp Ct S : Addr} {KL a c : Nat}, IPre s₀ Kp Ct S KL x (Z S) →
    EArgsS s₀ Kp Ct S KL a c s →
    WP isa (.call e.name e.code) s (EPostX s (Kp + BitVec.ofNat 64 a) (Ct + BitVec.ofNat 64 c) (KL / 2) (X S))
  ekRel : ∀ {s₀ s₀' : State} {Kp Ct S : Addr} {KL a c : Nat} {P : State → State → Prop},
    IPre s₀ Kp Ct S KL x (Z S) → IPre s₀' Kp Ct S KL x (Z S) → s₀.gpr .rsp = s₀'.gpr .rsp →
    (∀ u v, P u v → EArgsS s₀ Kp Ct S KL a c u ∧ EArgsS s₀' Kp Ct S KL a c v) →
    RelCT isa P (.call e.name e.code) fun _ _ => True
  sk : ∀ {s₀ s : State} {Kp Ct S : Addr} {KL : Nat}, IPre s₀ Kp Ct S KL x (Z S) → SArgsS s₀ Ct S KL x s →
    WP isa (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.X86_64.subkeys c)) s
      (SPostX s Ct (Ct + BitVec.ofNat 64 240) (KL / 8 + 6) (X S))
  skRel : ∀ {s₀ s₀' : State} {Kp Ct S : Addr} {KL : Nat} {P : State → State → Prop},
    IPre s₀ Kp Ct S KL x (Z S) → IPre s₀' Kp Ct S KL x (Z S) → s₀.gpr .rsp = s₀'.gpr .rsp →
    (∀ u v, P u v → SArgsS s₀ Ct S KL x u ∧ SArgsS s₀' Ct S KL x v) →
    RelCT isa P (.call ("vg_cmac_aes_subkeys" ++ sfx) (Impl.CmacAes.X86_64.subkeys c)) fun _ _ => True

theorem initSaved_slots : Spill.Slots initSaved := by decide

theorem initSaved_le : ∀ p ∈ initSaved, p.2 + 8 ≤ 256 := by decide

theorem initRestored_sub : ∀ p ∈ initRestored, p ∈ initSaved := by decide

theorem initRestored_fst {r : Reg} (h : r ∉ initRestored.map Prod.fst) : r ∉ initSaved.map Prod.fst := by
  intro h'; apply h
  simp only [initSaved, initRestored, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at h' ⊢
  rcases h' with h' | h' | h' | h' | h' <;> simp [h']

theorem init_wpG {x : BitVec 32} {e : Impl.Aes.X86_64.ExpandKey} {c : Impl.Aes.X86_64.Ctr32} {sfx : String}
    {Z X : Addr → Region} (T : ICall x e c sfx Z X) {s₀ : State} {Kp Ct S : Addr} {KL : Nat}
    (hp : IPre s₀ Kp Ct S KL x (Z S)) :
    WP isa (initAt x e c sfx) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.Siv.KeyRepr s'.mem Ct (Spec.Aes.bytesAt s₀.mem Kp KL) := by
  have hwC := hp.wC
  have hwK := hp.wK
  have hH := hp.half
  have cs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .rsp], r ∈ calleeSaved := by decide
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (T.ek hp h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, g₃, m₃, rd₃, wr₃⟩ := initMid₁_ok (s := s₂) x
    (by rw [g₂ _ (cs _ (by simp)), h₁.r12]) (by rw [g₂ _ (cs _ (by simp)), h₁.r13])
    (by rw [g₂ _ (cs _ (by simp)), h₁.r14])
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by rw [g₃ _ (cs _ (by simp)), g₂ _ (cs _ (by simp)), h₁.rsp]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, h₂.rd, h₁.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, h₂.wr, h₁.wr]
  refine WP.seq (WP.mono (T.sk hp (hp.sargs rdi₃ rsi₃ rdx₃ rcx₃ rsp₃ rd₃' wr₃')) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s₁.gpr r := by rw [h₄.saved r hr, g₃ r hr, g₂ r hr]
  obtain ⟨s₅, run₅, rdi₅, rsi₅, rdx₅, rcx₅, g₅, m₅, rd₅, wr₅⟩ := initMid₂_ok (s := s₄)
    (by rw [g₄ _ (cs _ (by simp)), h₁.rbx]) (by rw [g₄ _ (cs _ (by simp)), h₁.rbp])
    (by rw [g₄ _ (cs _ (by simp)), h₁.r12]) (by rw [g₄ _ (cs _ (by simp)), h₁.r13])
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by rw [g₅ _ (cs _ (by simp)), g₄ _ (cs _ (by simp)), h₁.rsp]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃']
  refine WP.seq (WP.mono (T.ek hp (hp.eargs (a := KL / 2) (c := 272) (by omega_arith) (by decide) rdi₅ rsi₅ rdx₅
    rcx₅ rsp₅ rd₅' wr₅')) fun s₆ h₆ => ?_)
  have g₆ (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₁.gpr r := by rw [h₆.saved r hr, g₅ r hr, g₄ r hr]
  have r13₆ : s₆.gpr .r13 = S := by rw [g₆ _ (cs _ (by simp)), h₁.r13]
  have xZ := T.sub S
  have sl := hp.slSub
  -- The memory, call by call.
  have f₁ : Frame [⟨S + BitVec.ofNat 64 160, 40⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact Spill.saveMem_frame _ _ _ _ fun p hp' => by
      simp only [initSaved, saveOff, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl <;> exact Offset.contains _ (by decide) (by decide) (by decide)
  have f₂ : Frame [⟨Ct, 240⟩, X S, below (s₀.gpr .rsp) 16] s₁.mem s₂.mem := by
    rw [← h₁.rsp]; simpa [k0] using h₂.frame
  have f₄ : Frame [⟨Ct + BitVec.ofNat 64 240, 32⟩, X S, below (s₀.gpr .rsp) 16] s₃.mem s₄.mem := by
    rw [← rsp₃]; exact h₄.frame
  have f₆ : Frame [⟨Ct + BitVec.ofNat 64 272, 240⟩, X S, below (s₀.gpr .rsp) 16] s₅.mem s₆.mem := by
    rw [← rsp₅]; exact h₆.frame
  -- The saved registers.
  have dSv {d : Nat} (hd : 160 ≤ d) (hd' : d + 8 ≤ 200) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, X S,
      below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨Ct + BitVec.ofNat 64 272, 240⟩]) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S + BitVec.ofNat 64 160, 40⟩ :=
      Offset.sub S hd (by omega_arith)
    have subZ : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ (Z S) := fun a h => sl a (sub a h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left subZ
    · exact (T.slots S).sub_left sub
    · exact hp.stk_s.symm.sub_left subZ
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left subZ
    · exact (hp.c_s.sub_left (hp.sC (by decide))).symm.sub_left subZ
  have sv₁ : Spill.Saved s₁.mem S s₀.gpr initSaved := by
    rw [h₁.mem]; exact Spill.saveMem_saved _ _ _ _ initSaved_slots
  have inSl (p : Reg × Nat) (hp' : p ∈ initSaved) : 160 ≤ p.2 ∧ p.2 + 8 ≤ 200 := by
    simp only [initSaved, saveOff, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;> decide
  have sv₆ : Spill.Saved s₆.mem S s₀.gpr initSaved := by
    refine ((sv₁.frame f₂ fun p hp' r hr => dSv (inSl p hp').1 (inSl p hp').2 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      (m' := s₄.mem) (by rw [← m₃]; exact f₄) fun p hp' r hr => dSv (inSl p hp').1 (inSl p hp').2 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).frame
      (by rw [← m₅]; exact f₆) fun p hp' r hr => dSv (inSl p hp').1 (inSl p hp').2 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)
  have inR : ∀ p ∈ initRestored, InRegions (s₆.rd ++ s₆.wr) (Spill.slot (s₆.gpr .r13) p.2) 8 := by
    intro p hp'
    have := inSl p (initRestored_sub p hp')
    rw [r13₆, h₆.rd, h₆.wr, rd₅', wr₅', hp.wr]
    exact ⟨Z S, by simp, hp.sIn this.1 this.2⟩
  refine WP.mono (Spill.restore_ok .r13 initRestored s₀.gpr s₆ (by decide) inR
    (by rw [r13₆]; exact fun p hp' => sv₆ p (initRestored_sub p hp'))) fun s₇ ⟨h₇a, h₇b, m₇, _, _⟩ => ?_
  have hRb : 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega_arith
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hm : r ∈ initRestored.map Prod.fst
    · exact h₇a r hm
    · rw [h₇b r hm, g₆ r hr, h₁.other r hr (initRestored_fst hm)]
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    have dR (r : Region) (hr : r ∈ [⟨Ct, 240⟩, X S, below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩,
        ⟨Ct + BitVec.ofNat 64 272, 240⟩, ⟨S + BitVec.ofNat 64 160, 40⟩]) :
        (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hp.ret_c.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_s.sub_right xZ
      · exact Offset.base_disjoint_below _ (by decide)
      · exact hp.ret_c.sub_right (hp.sC (by decide))
      · exact hp.ret_c.sub_right (hp.sC (by decide))
      · exact hp.ret_s.sub_right sl
    rw [m₇, f₆.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide), m₅,
      f₄.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide), m₃,
      f₂.readW c (fun r hr => dR r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
        (by decide),
      f₁.readW c (fun r hr => dR r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)]
  · rw [m₇]
    -- The key, outside everything the code writes.
    have dK {a n : Nat} (ha : a + n ≤ KL) (r : Region) (hr : r ∈ [⟨Ct, 240⟩, X S,
        below (s₀.gpr .rsp) 16, ⟨Ct + BitVec.ofNat 64 240, 32⟩, ⟨S + BitVec.ofNat 64 160, 40⟩]) :
        (⟨Kp + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := by
      have sub := hp.sK ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.k_c.sub_left sub).sub_right (Region.sub_prefix (by decide))
      · exact (hp.k_s.sub_left sub).sub_right xZ
      · exact (hp.stk_k.sub_right sub).symm
      · exact (hp.k_c.sub_left sub).sub_right (hp.sC (by decide))
      · exact (hp.k_s.sub_left sub).sub_right sl
    have key {a : Nat} (ha : a + KL / 2 ≤ KL) :
        Spec.Aes.bytesAt s₅.mem (Kp + BitVec.ofNat 64 a) (KL / 2) =
          Spec.Aes.bytesAt s₀.mem (Kp + BitVec.ofNat 64 a) (KL / 2) := by
      rw [m₅, bytesAt_frame f₄ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega_arith), m₃,
        bytesAt_frame f₂ (fun r hr => dK ha r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
          (by omega_arith),
        bytesAt_frame f₁ (fun r hr => dK ha r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega_arith)]
    have key₁ : Spec.Aes.bytesAt s₁.mem Kp (KL / 2) = Spec.Aes.bytesAt s₀.mem Kp (KL / 2) := by
      have := bytesAt_frame f₁ (fun r hr => dK (a := 0) (n := KL / 2) (by omega_arith) r (by simp only [List.mem_singleton] at hr; subst hr; simp)) (by omega_arith)
      rwa [k0] at this
    have key₂ := key (a := KL / 2) (by omega_arith)
    have sch : Spec.Aes.bytesAt s₂.mem Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp (KL / 2)) := by
      have := h₂.out; simp only [k0] at this; rw [this, key₁]
    refine keyRepr_of hp.klen ?_ ?_ ?_
    · rw [bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint Ct (by omega_arith) (by omega_arith)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega_arith))).sub_right xZ
          · exact (hp.stk_c.sub_right (Region.sub_prefix (by omega_arith))).symm) (by omega_arith), m₅,
        bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.base_disjoint Ct (by omega_arith) (by omega_arith)
          · exact (hp.c_s.sub_left (Region.sub_prefix (by omega_arith))).sub_right xZ
          · exact (hp.stk_c.sub_right (Region.sub_prefix (by omega_arith))).symm) (by omega_arith), m₃, sch]
    · rw [bytesAt_frame f₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.disjoint Ct (by omega_arith) (by omega_arith) (by omega_arith)
          · exact (hp.c_s.sub_left (hp.sC (by decide))).sub_right xZ
          · exact (hp.stk_c.sub_right (hp.sC (by decide))).symm) (by decide), m₅, h₄.out, m₃,
        show 16 * (KL / 8 + 6 + 1) = 16 * (Spec.Aes.rounds (KL / 2 / 4) + 1) by
          simp only [Spec.Aes.rounds]; omega_arith, sch]
    · rw [h₆.out, key₂]

/-! ## Constant time -/

/-- What each call leaves for the code after it: the registers that hold
the arguments of the next one. -/
structure IAfter (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = Kp
  rbp : s.gpr .rbp = BitVec.ofNat 64 (KL / 2)
  r12 : s.gpr .r12 = Ct
  r13 : s.gpr .r13 = S
  r14 : s.gpr .r14 = BitVec.ofNat 64 (KL / 8 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem IAfter.keep {s₀ s s' : State} {Kp Ct S : Addr} {KL : Nat} (h : IAfter s₀ Kp Ct S KL s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    IAfter s₀ Kp Ct S KL s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.rsp],
    by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem IMid₁.after {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} (h : IMid₁ s₀ Kp Ct S KL s) :
    IAfter s₀ Kp Ct S KL s :=
  ⟨h.rbx, h.rbp, h.r12, h.r13, h.r14, h.rsp, h.rd, h.wr⟩

theorem initMid₁_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z) (h : IAfter s₀ Kp Ct S KL s) :
    WP isa (.block (initMid₁At x)) s fun s' => SArgsS s₀ Ct S KL x s' ∧ IAfter s₀ Kp Ct S KL s' := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, g, _, rd, wr⟩ := initMid₁_ok x h.r12 h.r13 h.r14
  have h' := h.keep g rd wr
  exact WP.of_runBlock ⟨s', run, hp.sargs rdi rsi rdx rcx h'.rsp h'.rd h'.wr, h'⟩

/-- The arguments of the second call of `vg_aes_expand_key_scratch`, and the
registers the code after it uses. -/
abbrev IEk (s₀ : State) (Kp Ct S : Addr) (KL : Nat) (s : State) : Prop :=
  EArgsS s₀ Kp Ct S KL (KL / 2) 272 s ∧ s.gpr .r13 = S

theorem initMid₂_wp {s₀ s : State} {Kp Ct S : Addr} {KL : Nat} {x : BitVec 32} {Z : Region}
    (hp : IPre s₀ Kp Ct S KL x Z) (h : IAfter s₀ Kp Ct S KL s) :
    WP isa (.block initMid₂) s fun s' => IEk s₀ Kp Ct S KL s' := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, g, _, rd, wr⟩ := initMid₂_ok h.rbx h.rbp h.r12 h.r13
  have h' := h.keep g rd wr
  exact WP.of_runBlock ⟨s', run, hp.eargs (by omega_arith) (by decide) rdi rsi rdx rcx h'.rsp h'.rd h'.wr, h'.r13⟩

theorem init_relG {x : BitVec 32} {e : Impl.Aes.X86_64.ExpandKey} {c : Impl.Aes.X86_64.Ctr32} {sfx : String}
    {Z X : Addr → Region} (T : ICall x e c sfx Z X)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) (.block (initMid₁At x))
      h).isSome = true)
    {s₀ s₀' : State} {Kp Ct S : Addr} {KL : Nat} (hp : IPre s₀ Kp Ct S KL x (Z S))
    (hp' : IPre s₀' Kp Ct S KL x (Z S)) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (initAt x e c sfx) fun _ _ => True := by
  have q2 : s₀.gpr .rdi = s₀'.gpr .rdi := by rw [hp.rdi, hp'.rdi]
  have q3 : s₀.gpr .rsi = s₀'.gpr .rsi := BitVec.eq_of_toNat_eq (by rw [hp.rsi, hp'.rsi])
  have q4 : s₀.gpr .rdx = s₀'.gpr .rdx := by rw [hp.rdx, hp'.rdx]
  have q5 : s₀.gpr .rcx = s₀'.gpr .rcx := by rw [hp.rcx, hp'.rcx]
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ := hB
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) (.block initMid₂)
      h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have agree (a b : State) (h : IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) :
      taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .rsp]) a b := by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.1.rbx, h.2.rbx]
    · rw [h.1.rbp, h.2.rbp]
    · rw [h.1.r12, h.2.r12]
    · rw [h.1.r13, h.2.r13]
    · rw [h.1.r14, h.2.r14]
    · rw [h.1.rsp, h.2.rsp, q1]
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := IMid₁ s₀ Kp Ct S KL) (F₂ := IMid₁ s₀' Kp Ct S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩
  have e₁ := (T.ekRel (P := fun a b => IMid₁ s₀ Kp Ct S KL a ∧ IMid₁ s₀' Kp Ct S KL b) hp hp' q1
    fun a b h => ⟨h.1.args, h.2.args⟩).wp
    (F₁ := IAfter s₀ Kp Ct S KL) (F₂ := IAfter s₀' Kp Ct S KL) fun a b h =>
      ⟨WP.mono (T.ek hp h.1.args) fun _ h₂ => h.1.after.keep h₂.saved h₂.rd h₂.wr,
        WP.mono (T.ek hp' h.2.args) fun _ h₂ => h.2.after.keep h₂.saved h₂.rd h₂.wr⟩
  have m₁ := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) _
    agree hB).wp
    (F₁ := fun (s : State) => SArgsS s₀ Ct S KL x s ∧ IAfter s₀ Kp Ct S KL s)
    (F₂ := fun (s : State) => SArgsS s₀' Ct S KL x s ∧ IAfter s₀' Kp Ct S KL s)
    fun a b h => ⟨initMid₁_wp hp h.1, initMid₁_wp hp' h.2⟩
  have sk := (T.skRel (P := fun a b => (SArgsS s₀ Ct S KL x a ∧ IAfter s₀ Kp Ct S KL a) ∧
      SArgsS s₀' Ct S KL x b ∧ IAfter s₀' Kp Ct S KL b) hp hp' q1
    fun a b h => ⟨h.1.1, h.2.1⟩).wp
    (F₁ := IAfter s₀ Kp Ct S KL) (F₂ := IAfter s₀' Kp Ct S KL)
    fun a b h => ⟨WP.mono (T.sk hp h.1.1) fun _ h₂ => h.1.2.keep h₂.saved h₂.rd h₂.wr,
      WP.mono (T.sk hp' h.2.1) fun _ h₂ => h.2.2.keep h₂.saved h₂.rd h₂.wr⟩
  have m₂ := (RelCT.taint (A := taint) (P := fun a b => IAfter s₀ Kp Ct S KL a ∧ IAfter s₀' Kp Ct S KL b) _
    agree hC).wp
    (F₁ := IEk s₀ Kp Ct S KL) (F₂ := IEk s₀' Kp Ct S KL)
    fun a b h => ⟨initMid₂_wp hp h.1, initMid₂_wp hp' h.2⟩
  have e₂ := (T.ekRel (P := fun a b => IEk s₀ Kp Ct S KL a ∧ IEk s₀' Kp Ct S KL b) hp hp' q1
    fun a b h => ⟨h.1.1, h.2.1⟩).wp
    (F₁ := fun (s : State) => s.gpr .r13 = S) (F₂ := fun (s : State) => s.gpr .r13 = S)
    fun a b h => ⟨WP.mono (T.ek hp h.1.1) fun _ h₂ => by rw [h₂.saved _ (by decide), h.1.2],
      WP.mono (T.ek hp' h.2.1) fun _ h₂ => by rw [h₂.saved _ (by decide), h.2.2]⟩
  have p := RelCT.taint (A := taint) (P := fun a b => a.gpr .r13 = S ∧ b.gpr .r13 = S) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1, h.2]) hD
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((m₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))))

/-! ## The instances -/

/-- Over any implementation of AES, with all of the working space. -/
theorem ICall.base (v : Ctr32Impl) :
    ICall (BitVec.ofNat 32 csOff) v.expand v.callee v.suffix (fun S => ⟨S, 2560⟩)
      (fun S => ⟨S + BitVec.ofNat 64 256, 2176⟩) := by
  have sS : ∀ S : Addr, Region.Sub ⟨S + BitVec.ofNat 64 256, 2176⟩ ⟨S, 2560⟩ := fun S => Offset.sub_base S (by decide)
  have sb : ∀ S : Addr, S + BitVec.signExtend 64 (BitVec.ofNat 32 csOff) = S + BitVec.ofNat 64 256 := fun S => by
    rw [csOff, sx_ofNat (by decide)]
  have eargs {s₀ s : State} {Kp Ct S : Addr} {KL a c : Nat}
      (hp : IPre s₀ Kp Ct S KL (BitVec.ofNat 32 csOff) ⟨S, 2560⟩) (h : EArgsS s₀ Kp Ct S KL a c s) :
      EArgs s (Kp + BitVec.ofNat 64 a) (Ct + BitVec.ofNat 64 c) (S + BitVec.ofNat 64 256) (KL / 2) :=
    have s5 : Region.Sub ⟨S + BitVec.ofNat 64 256, 512⟩ ⟨S, 2560⟩ := Offset.sub_base S (by decide)
    h.args.full h.rcx ((hp.k_s.sub_left (hp.sK h.ha)).sub_right s5)
      ((hp.c_s.sub_left (hp.sC h.hc)).sub_right s5)
      (by rw [h.rsp]; exact hp.stk_s.sub_right s5)
      (by
        rw [h.wr, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩)
  have sargs {s₀ s : State} {Kp Ct S : Addr} {KL : Nat}
      (hp : IPre s₀ Kp Ct S KL (BitVec.ofNat 32 csOff) ⟨S, 2560⟩) (h : SArgsS s₀ Ct S KL (BitVec.ofNat 32 csOff) s) :
      SArgs s Ct (Ct + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 256) (KL / 8 + 6) := by
    have a := h.args
    rw [sb] at a
    exact a.full ((hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (sS S))
      ((hp.c_s.sub_left (hp.sC (by decide))).sub_right (sS S))
      (by rw [h.rsp]; exact hp.stk_s.sub_right (sS S))
      (by have := hp.wZ; simp only at this; rw [toNat_add_lt S this (by decide)]; omega)
      (by
        rw [h.wr, hp.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩)
  exact
  { sub := sS
    slots := fun S => Offset.disjoint S (by decide) (by decide) (by decide)
    ek := fun {_ _ _ _ S _ _ _} hp h => WP.mono (ek_call v (eargs hp h)) fun _ h' =>
      h'.x (Offset.sub S (by decide) (by decide))
    ekRel := fun hp hp' q h => ek_rel v fun a b hab =>
      ⟨_, _, _, _, eargs hp (h a b hab).1, eargs hp' (h a b hab).2, by
        rw [(h a b hab).1.rsp, (h a b hab).2.rsp, q]⟩
    sk := fun hp h => WP.mono (sub_call v _ (sargs hp h)) fun _ h' => h'.x fun _ h => h
    skRel := fun hp hp' q h => sub_rel v _ fun a b hab =>
      ⟨_, _, _, _, sargs hp (h a b hab).1, sargs hp' (h a b hab).2, by
        rw [(h a b hab).1.rsp, (h a b hab).2.rsp, q]⟩ }

/-- `initFOff` from `S`, plus 2048, is `S + 200`, after our saved registers. -/
theorem initFOff_add (S : Addr) {d : Nat} (h : 1848 ≤ d) :
    S + BitVec.signExtend 64 initFOff + BitVec.ofNat 64 d = S + BitVec.ofNat 64 (d - 1848) := by
  rw [show BitVec.signExtend 64 initFOff = -BitVec.ofNat 64 1848 by decide, ← BitVec.sub_eq_add_neg,
    sub_add_ofNat _ h]

/-- Over an implementation of `vg_aes_ctr32` that needs no working space, with
`vg_aes_expand_key_scratch_aesni`, which needs none either: only the 72
bytes at `S + saveOff`, of which the calls write the last 32. -/
theorem ICall.free (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ICall initFOff ekF v.callee v.suffix (fun S => ⟨S + BitVec.ofNat 64 160, 72⟩)
      (fun S => ⟨S + BitVec.ofNat 64 200, 32⟩) where
  sub S := Offset.sub S (by decide) (by decide)
  slots S := Offset.disjoint S (by decide) (by decide) (by decide)
  ek _ h := ek_callF h.args
  ekRel _ _ q h := ek_relF fun a b hab =>
    ⟨_, _, _, (h a b hab).1.args, (h a b hab).2.args, by rw [(h a b hab).1.rsp, (h a b hab).2.rsp, q]⟩
  sk {_ _ _ _ S _} _ h := by
    have := sub_callF v f ("vg_cmac_aes_subkeys" ++ v.suffix) h.args
    rwa [initFOff_add S (by decide)] at this
  skRel _ _ q h := sub_relF v f _ fun a b hab =>
    ⟨_, _, _, _, (h a b hab).1.args, (h a b hab).2.args, by rw [(h a b hab).1.rsp, (h a b hab).2.rsp, q]⟩

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' :=
  init_wpG (ICall.base v) (IPre.of h0)

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initX86_64.pre initX86_64.pub (init v.expand v.callee v.suffix) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp' : IPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat (BitVec.ofNat 32 csOff)
      ⟨s₀.gpr .rcx, 2560⟩ := by
    rw [q2, q3, q4, q5]; exact IPre.of h₂
  exact (init_relG (ICall.base v) ⟨_, by taint_decide⟩ (IPre.of h₁) hp' q1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Without working space for the functions called -/

/-- `initX86_64` with a working space of 72 bytes, for `initF`. -/
def initX86_64F : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 512⟩
    let scr : Region := ⟨s.gpr .rcx, 72⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 512 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 72 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 32 ∨ (s.gpr .rsi).toNat = 48 ∨ (s.gpr .rsi).toNat = 64)
  post := initX86_64.post
  pub := initX86_64.pub

/-- What the `sub` before `initAt` leaves. -/
def SubF (s₀ s : State) : Prop :=
  s.gpr .rcx = s₀.gpr .rcx - BitVec.ofNat 64 160 ∧ (∀ r, r ≠ .rcx → s.gpr r = s₀.gpr r) ∧
    s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

theorem subF_ok (s₀ : State) :
    ∃ s₁, runBlock isa [.alu .sub .rcx (imm saveOff)] s₀ = some s₁ ∧ SubF s₀ s₁ := by
  refine ⟨_, by simp only [runBlock_cons, exec, readSrc, execAlu]; rfl, ?_⟩
  simp only [SubF, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ↓reduceIte]
  exact ⟨by rw [show BitVec.signExtend 64 (BitVec.ofNat 32 saveOff) = BitVec.ofNat 64 160 by decide],
    fun r h => by simp [h], trivial, trivial, trivial⟩

theorem IPre.ofF {s₀ s₁ : State} (h : initX86_64F.pre s₀) (hs : SubF s₀ s₁) :
    IPre s₁ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx - BitVec.ofNat 64 160) (s₀.gpr .rsi).toNat initFOff
      ⟨s₀.gpr .rcx - BitVec.ofNat 64 160 + BitVec.ofNat 64 160, 72⟩ := by
  obtain ⟨rcx, g, _, rd, wr⟩ := hs
  obtain ⟨a, b, c, d, e, f, g', h, i, j, k, l, m, n, o, p⟩ := h
  have e0 : s₀.gpr .rcx - BitVec.ofNat 64 160 + BitVec.ofNat 64 160 = s₀.gpr .rcx := BitVec.sub_add_cancel _ _
  have sp := g .rsp (by decide)
  rw [e0]
  refine ⟨g _ (by decide), by rw [g _ (by decide)], g _ (by decide), rcx, by rw [sp]; exact a,
    by rw [rd]; exact b, by rw [wr]; exact c, d, e, f, by rw [sp]; exact g', by rw [sp]; exact h,
    by rw [sp]; exact i, by rw [sp]; exact j, by rw [sp]; exact k, by rw [sp]; exact l, m, n, o, p,
    fun h₁ h₂ => ?_, fun h₁ h₂ => ?_, ?_⟩
  · rw [sub_add_ofNat _ h₁]; exact Offset.contains_base _ (by omega) (by omega)
  · rw [initFOff_add _ (by omega), sub_add_ofNat _ (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [initFOff_add _ (by decide), sub_add_ofNat _ (by decide)]
    rw [toNat_add_lt _ o (by decide)]; omega

theorem initF_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ : State} (h0 : initX86_64F.pre s₀) :
    WP isa (initF ekF v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64F.post s₀ s' := by
  obtain ⟨s₁, run₁, hs⟩ := subF_ok s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hp := IPre.ofF h0 hs
  obtain ⟨_, g₁, m₁, _, _⟩ := hs
  refine WP.mono (init_wpG (ICall.free v f) hp) fun s' ⟨⟨hg, hr⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hg r hr', g₁ r (by rintro rfl; simp [calleeSaved] at hr')]
  · rw [← g₁ .rsp (by decide), hr, m₁]
  · rw [m₁] at hpost; exact hpost

theorem initF_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ConstantTime isa initX86_64F.pre initX86_64F.pub (initF ekF v.callee v.suffix) := by
  intro s₀ s₀' _ _ _ _ h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (.block [.alu .sub .rcx (imm saveOff)]) h).isSome = true := ⟨_, by taint_decide⟩
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
  have r : RelCT isa (fun a b => SubF s₀ a ∧ SubF s₀' b) (initAt initFOff ekF v.callee v.suffix)
      fun _ _ => True := by
    intro x y t t' x' y' ⟨hx, hy⟩ ex ey
    have hp := IPre.ofF h₁ hx
    have hp' := IPre.ofF h₂ hy
    rw [← q2, ← q3, ← q4, ← q5] at hp'
    exact init_relG (ICall.free v f) ⟨_, by taint_decide⟩ hp hp'
      (by rw [hx.2.1 _ (by decide), hy.2.1 _ (by decide), q1]) _ _ _ _ _ _ ⟨rfl, rfl⟩ ex ey
  exact ((a.mono (fun _ _ h => h) fun _ _ h => h.2).seq r _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.X86_64
