module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

/-! # Shared stack arguments and scratch setup for x86 point conversion -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

structure InputPre (c : Cfg) (len : Nat) (s : State) : Prop where
  pk : (⟨ptr s 1, len⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨ptr s 2, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨ptr s 1, len⟩ ⟨ptr s 2, size⟩
  pk_fit : (arg s 1).toNat + len ≤ 2 ^ 32
  ws_fit : (arg s 2).toNat + size ≤ 2 ^ 32
  args : (⟨argAddr s 0, 12⟩ : Region) ∈ s.rd ++ s.wr
  args_sc : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨ptr s 2, size⟩
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_lo : c.stk ≤ (s.gpr .esp).toNat
  stk_sc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 c.stk, c.stk⟩ ⟨ptr s 2, size⟩

theorem args_idx {i : Nat} (hi : i ∈ Impl.EcKey.Compressed.X86.args.idx) : i < 3 := by
  simp only [Impl.EcKey.Compressed.X86.args, Args.idx, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

theorem input_setup {c : Cfg} {len : Nat} {s : State}
    (hp : InputPre c len s) (hlen : c.C.len ≤ len) :
    SetupPre c Impl.EcKey.Compressed.X86.args s := by
  have hfit := hp.pk_fit
  have hi : ∀ e, e + 4 ≤ c.C.len → InRegions (s.rd ++ s.wr) (ptr s 1 + BitVec.ofNat 64 e) 4 :=
    fun _ he => ⟨_, hp.pk, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨ptr s 1, c.C.len⟩ ⟨ptr s 2, size⟩ :=
    hp.disjoint.sub_left (by simpa using Region.sub_prefix hlen)
  refine ⟨.inl rfl, hp.ws, ?_, ?_, ?_, hi, hi, hi, hd, hd, hd,
    by change (arg s 1).toNat + c.C.len ≤ 2 ^ 32; have := hp.pk_fit; omega,
    by change (arg s 1).toNat + c.C.len ≤ 2 ^ 32; have := hp.pk_fit; omega,
    by change (arg s 1).toNat + c.C.len ≤ 2 ^ 32; have := hp.pk_fit; omega,
    hp.ws_fit, ?_, hp.sp_lo, hp.stk_sc⟩
  · intro i h
    exact ⟨_, hp.args, arg_containsN (k := 3) (by have := hp.sp_fit; omega) (args_idx h)⟩
  · intro i h
    exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega) (args_idx h))
  · intro i h
    have := args_idx h
    have := hp.sp_fit
    omega
  · exact stkOk_of (Cfg.stk_ge c) hp.sp_lo
      (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := hp.ws_fit; omega)]; exact hp.ws_fit)
      (by decide) hp.stk_sc

theorem setup_fixed {c : Cfg} {s₀ s : State} {base : Addr}
    (P : SetupPost c Impl.EcKey.Compressed.X86.args s₀ base s) : Fixed c base s₀.gpr s.mem :=
  ⟨P.consts (MP, c.C.p) (by simp [Cfg.consts]), P.consts (MN, c.C.n) (by simp [Cfg.consts]),
    P.consts (ZERO, 0) (by simp [Cfg.consts]), P.consts (ONE, 1) (by simp [Cfg.consts]),
    (P.consts (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
    P.consts (AP, c.mont c.C.a) (by simp [Cfg.consts]),
    P.consts (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
    P.consts (GX, c.mont c.C.gx) (by simp [Cfg.consts]),
    P.consts (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
    P.consts (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]),
    P.consts (ONEN, c.R % c.C.n) (by simp [Cfg.consts]), P.saved, P.table⟩

end VG.Proof.EcKey.Compressed.X86
