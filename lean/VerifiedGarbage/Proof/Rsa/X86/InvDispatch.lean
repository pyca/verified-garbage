module
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.InvGate
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Rsa.X86.InvStep
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.X86.CvInverseCall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseCall
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # Public-length selection of the verified batched inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
 VG.Proof.Weierstrass VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)
open VG.Impl.Rsa.X86.CrtValuesRt (lay)
open VG.Impl.Rsa.X86.CrtValues (nArr)
open VG.Proof.Weierstrass.X86.Inv (wordClob)

 def inverseM (P : Nat) := 2*(P/2)+1
 structure InvInput (args : Nat → BitVec 32) (base : Addr) (size len P Q : Nat) (s : State) : Prop where
  ws : RtWs lay s base size len nArr
  gate : InvGate args base size P Q s
  u : num s.mem base (kw len) 0=Q
  m : num s.mem base (kw len) aM=inverseM P
  nm : num s.mem base (kw len) aNM+inverseM P=2^(32*kw len)
  zero : num s.mem base (kw len) aZero=0
  bank : bank s.mem base (kw len) 0=(Q,inverseM P,1,0)

 /-- The arrays the inverse may change: its own, and the modulus `m` and `2^(32 w) - m`, which the
 general inverse sets to 3 and `2^(32 w) - 3` where `m` is 1. -/
 abbrev invOut : List Nat := invArrs ++ [aM, aNM]

 /-- What the inverse leaves: its frame lets the stack below `esp` that the general inverse's call
 uses change too. -/
 def InvPost (base : Addr) (size len P Q : Nat) (s t : State) : Prop :=
  RtWs lay t base size len nArr ∧
  VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS base (s.gpr .esp) (ranges (kw len) invOut (invSlots ++ rtSlots))
    s.mem t.mem ∧
  Keeps wordClob s t ∧
  (1<inverseM P → num t.mem base (kw len) 1=Nat.gcd Q (inverseM P) ∧
   (inverseM P : Int)∣(num t.mem base (kw len) 3 : Int)*Q-num t.mem base (kw len) 1 ∧
   num t.mem base (kw len) 3<inverseM P)

 theorem InvInput.rest {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s t : State} {regs : List Reg}
    (h : InvInput args base size len P Q s) (K : Keeps regs s t) (di : .edi∉regs) (sp : .esp∉regs)
    (mem : t.mem=s.mem) : InvInput args base size len P Q t := by
  have O : Outside base 0 size s.mem t.mem := by rw [mem]; exact Outside.refl _ _ _ _
  exact ⟨h.ws.keep K di sp O,h.gate.keep K sp O,mem ▸ h.u,mem ▸ h.m,mem ▸ h.nm,mem ▸ h.zero,mem ▸ h.bank⟩

 /-- What the call's setup leaves: the call's input, with the modulus 3 where it was 1. -/
 theorem callSetup_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.CrtValuesRt.callSetup s fun v =>
      CallAt base size len (args 7).toNat v ∧ v.gpr .esp = s.gpr .esp ∧
      Keep base (kw len) [1, aM, aNM] [VG.Impl.Rsa.X86.CrtValuesRt.sOne] s.mem v.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s v ∧
      num v.mem base (kw len) aM = (if inverseM P = 1 then 3 else inverseM P) ∧
      num v.mem base (kw len) 0 = Q := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  have b := h.bank
  simp only [bank, Prod.mk.injEq] at b
  obtain ⟨b0, -, b2, b3⟩ := b
  have odd : num s.mem base (kw len) aM % 2 = 1 := by rw [h.m]; unfold inverseM; omega
  unfold VG.Impl.Rsa.X86.CrtValuesRt.callSetup
  refine WP.seq (WP.mono (modulusAbove_ok h.ws (by decide) odd b2 h.zero) fun u ⟨hu, ku, ru, mu, vu, nu⟩ => ?_)
  obtain ⟨a, ha, hka, LA⟩ := hu.lenArg
  change kw a = kw len at hka
  have ga : a = (args 7).toNat := by
    have nArg := h.gate.nArg.keep ru (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws.ws ku (by decide) (by decide))
    have eq : BitVec.ofNat 32 a = args 7 := Option.some.inj (LA.readSrc.symm.trans nArg.readSrc)
    have ae := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ae
    exact ae
  subst ga
  unfold VG.Impl.Rsa.X86.CrtValuesRt.inverseArgs
  refine VG.Proof.RsaKeyGen.X86.KeyRuntime.callSetup_ok (L := lay) LA.readSrc ha fun v Kv mv eax ecx => ?_
  have hv : RtWs lay v base size len nArr :=
    hu.keep Kv (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  have espV : v.gpr .esp = s.gpr .esp := (Kv.1 .esp (by decide)).trans (ru.1 .esp (by decide))
  have kept {j : Nat} (hj : j < nArr) (out : j ∉ [1, aM, aNM]) :
      num v.mem base (kw len) j = num s.mem base (kw len) j := by
    rw [mv]
    exact ku.num (fun k hk e => out (e ▸ hk)) (by decide) (fit j hj)
  have mV : num v.mem base (kw len) aM = (if inverseM P = 1 then 3 else inverseM P) := by rw [mv, mu, h.m]
  refine ⟨⟨hv, espV ▸ h.gate.room, ha, hka, eax, ecx, ?_, ?_, by rw [mv]; exact vu,
      by rw [kept (by decide) (by decide), b2], by rw [kept (by decide) (by decide), b3], by rw [mv]; exact nu,
      by rw [kept (by decide) (by decide), h.zero]⟩, espV, mv ▸ ku, ru.trans (Kv.mono (by decide)), mV,
    by rw [kept (by decide) (by decide), b0]⟩
  · rw [mV]; unfold inverseM; split <;> omega
  · rw [mV]; unfold inverseM; split <;> omega

 theorem inverseFallback_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.CrtValuesRt.fallback s (InvPost base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.CrtValuesRt.fallback
  refine WP.seq (WP.mono (callSetup_ok h) fun v ⟨C, espV, kv, rv, mV, qV⟩ => ?_)
  refine WP.mono (call_ok C) fun t ⟨ht, O, G, Bz, Lt, Kt⟩ => ?_
  rw [espV] at O
  refine ⟨ht, ?_, (rv.mono (by decide)).trans (Kt.mono (by decide)), ?_⟩
  · exact (VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs kv).mono (ranges_sub (by decide) (by decide)) |>.trans
      (O.mono (ranges_sub (by decide) (by decide)))
  · intro large
    have mM : num v.mem base (kw len) aM = inverseM P := by rw [mV, ite_eq_right_iff.mpr (by omega)]
    rw [mM, qV] at G Bz
    rw [mM] at Lt
    exact ⟨G, Bz, Lt⟩

 /-- The body's writes are within the inverse's arrays and the header words from 16 on. -/
 theorem body_keep {base : Addr} {len : Nat} {m m' : Mem} (hpos : 0 < kw len)
    (U : Unch base (VG.Proof.Rsa.X86.InvBatchRt.bodyWrites len) m m') :
    Keep base (kw len) invArrs (invSlots ++ rtSlots) m m' := by
  intro x hx
  apply U x
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq len
  have harr : ∀ j ∈ invArrs, ofs base x < arr (kw len) j ∨ arr (kw len) j + S (kw len) ≤ ofs base x :=
    fun j hj => hx _ (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨j, hj, rfl⟩)
  have hsl : ∀ d ∈ invSlots ++ rtSlots, ofs base x < d ∨ d + 4 ≤ ofs base x :=
    fun d hd => hx _ (by simp only [ranges, List.mem_append, List.mem_map]; exact .inr ⟨d, List.mem_append.mp hd, rfl⟩)
  have hS : S (kw len) = 8 * VG.Proof.Rsa.X86.InvBatchRt.nw len + 8 := by
    show 4 * (kw len + 2) = _; omega
  have ra (j : Nat) : VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a j) =
      arr (kw len) j := by
    show VG.Impl.Rsa.X86.InvBatchRt.offset (kw len) j + 0 * (2 * kw len) + 0 = _
    rw [VG.Proof.Rsa.X86.InvBatchRt.offset_eq]; simp
  -- A byte in one of the ranges is in a word or an array of the frame.
  have words : ∀ k < 22, 16 + 4 * k ∈ invSlots ++ rtSlots := by decide
  have arrs0 : ∀ j < 8, j ∈ invArrs := by decide
  have arrs11 : ∀ j < 4, 11 + j ∈ invArrs := by decide
  have inArr (lo j₀ c : Nat) (hc : ∀ j < c, j₀ + j ∈ invArrs) (hlo : lo = arr (kw len) j₀)
      (h₁ : lo ≤ ofs base x) (h₂ : ofs base x < lo + c * S (kw len)) : False := by
    have Spos : 0 < S (kw len) := by omega
    obtain ⟨j, hj⟩ : ∃ j, j = (ofs base x - lo) / S (kw len) := ⟨_, rfl⟩
    have hq := Nat.div_add_mod (ofs base x - lo) (S (kw len))
    have hr := Nat.mod_lt (ofs base x - lo) Spos
    rw [← hj] at hq
    have hcS := Nat.mul_comm c (S (kw len))
    have hjc : j < c := by
      apply Nat.lt_of_mul_lt_mul_left (a := S (kw len))
      omega
    have e : arr (kw len) (j₀ + j) = lo + S (kw len) * j := by
      rw [hlo]; simp only [arr, Nat.add_mul]; rw [Nat.mul_comm j]; omega
    have := harr (j₀ + j) (hc j hjc)
    rw [e] at this
    omega
  intro w hw
  simp only [VG.Proof.Rsa.X86.InvBatchRt.bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
  have e16 : VG.Impl.Rsa.X86.InvBatchRt.win = 16 := rfl
  rcases hw with rfl | rfl | rfl
  · change ofs base x < VG.Impl.Rsa.X86.InvBatchRt.win ∨ VG.Impl.Rsa.X86.InvBatchRt.win + 88 ≤ ofs base x
    by_contra hc
    have := hsl (16 + 4 * ((ofs base x - 16) / 4)) (words _ (by omega))
    omega
  · change ofs base x < _ ∨ _ + _ ≤ ofs base x
    by_contra hc
    rw [ra, ← hS] at hc
    exact inArr _ 0 8 (fun j hj => by simpa using arrs0 j hj) rfl (by omega) (by omega)
  · change ofs base x < _ ∨ _ + _ ≤ ofs base x
    by_contra hc
    rw [ra, ← hS] at hc
    exact inArr _ 11 4 (fun j hj => arrs11 j hj) rfl (by omega) (by omega)

 theorem inverseBodyRt_ok [VG.Proof.Rsa.X86.BatchLaw] {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) (hn2 : 2 ≤ VG.Proof.Rsa.X86.InvBatchRt.nw len)
    (he : VG.Proof.Rsa.X86.InvBatchRt.nw len % 2 = 0)
    (pb : (args 9).toNat ≤ 4 * VG.Proof.Rsa.X86.InvBatchRt.nw len)
    (qb : (args 11).toNat ≤ 4 * VG.Proof.Rsa.X86.InvBatchRt.nw len) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.body lay) s (InvPost base size len P Q s) := by
  have hs := h.ws.ws.workspace
  have nw := hs.nowrap
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq len
  let n := VG.Proof.Rsa.X86.InvBatchRt.nw len
  have ra (j : Nat) : VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a j) =
      arr (kw len) j := by
    show VG.Impl.Rsa.X86.InvBatchRt.offset (kw len) j + 0 * (2 * kw len) + 0 = _
    rw [VG.Proof.Rsa.X86.InvBatchRt.offset_eq]; simp
  have pc : inverseM P < 2 ^ (32 * n) := odd_modulus_bound (by omega) (prime_bound h.gate.pBound pb)
  have qc : Q < 2 ^ (32 * n) := prime_bound h.gate.qBound qb
  have mv : val32 s.mem base (VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 8)) n =
      inverseM P := by
    rw [ra]
    change val32 s.mem base (arr (kw len) aM) n = inverseM P
    have v : val32 s.mem base (arr (kw len) aM) (kw len) = inverseM P := h.m
    rw [prefix_eq (w := kw len) (by omega) (by rw [v]; exact pc), v]
  have qv : val32 s.mem base (VG.Proof.Rsa.X86.InvBatchRt.rv (kw len) (VG.Impl.Rsa.X86.InvBatchRt.a 0)) n = Q := by
    rw [ra]
    have v : val32 s.mem base (arr (kw len) 0) (kw len) = Q := h.u
    rw [prefix_eq (w := kw len) (by omega) (by rw [v]; exact qc), v]
  refine WP.mono (VG.Proof.Rsa.X86.BatchLaw.inv_ok h.ws (by decide) hn2 he mv qv (by unfold inverseM; omega))
    fun t ⟨_, G, A, small, R, O⟩ => ?_
  have bankKeep := body_keep h.ws.ws.wpos O
  have outside := keep_outside h.ws.ws bankKeep (by decide) (by decide)
  refine ⟨h.ws.keep R (by decide) (by decide) outside,
    VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs (bankKeep.mono (by decide) (by decide)), R, ?_⟩
  intro large
  have vm : VG.Proof.Rsa.X86.InvBatchRt.virtualMod (inverseM P) = inverseM P := by
    unfold VG.Proof.Rsa.X86.InvBatchRt.virtualMod; rw [ite_eq_right (by omega)]
  simp only [vm, ra] at G A small
  change num t.mem base (kw len) 1 = Nat.gcd (inverseM P) Q at G
  change (inverseM P : Int) ∣ (num t.mem base (kw len) 3 : Int) * Q - (Nat.gcd (inverseM P) Q : Int) at A
  change num t.mem base (kw len) 3 < inverseM P at small
  refine ⟨G.trans (Nat.gcd_comm _ _), ?_, small⟩
  rw [G]; exact A

end VG.Proof.Rsa.X86.CrtValuesRt
