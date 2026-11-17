module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashStep
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration

/-! ### `Dsa.X86_64.Generation.HashSequence`, which this module and modules that import it used -/

section

/-! # All p-candidate hash contributions, with bounded public sequencing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem hashPrefix_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) (k : Nat) (hk : k ≤ p.count + 1)
    {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashPrefix G p.len p.count k) s fun t =>
      HashState p Hs k t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame p.changed s.mem t.mem := by
  induction k generalizing s with
  | zero =>
    unfold Impl.Dsa.X86_64.Generation.pHashPrefix
    have he : WP isa (.block []) s (fun t => t = s) := by xrun
    exact WP.mono he fun t h => by
      subst t
      exact ⟨hs, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ k ih =>
    unfold Impl.Dsa.X86_64.Generation.pHashPrefix
    refine WP.seq (WP.mono (ih (by omega_using [hk]) hs) fun u ⟨hu, rdu, wru, csu, hfu⟩ => ?_)
    refine WP.mono (hashStep_ok hG hHh hsize hd (by omega_using [hk]) hu) fun t ⟨ht, rdt, wrt, cst, hft⟩ => ?_
    exact ⟨ht, rdt.trans rdu, wrt.trans wru, fun r hr => (cst r hr).trans (csu r hr), hfu.trans hft⟩

theorem pHashes_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p Hs 0 s) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashes G p.len p.count) s fun t =>
      HashState p Hs (p.count + 1) t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame p.changed s.mem t.mem :=
  hashPrefix_ok hG hHh hsize hd _ (Nat.le_refl _) hs

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PShape`, which only this module used -/

section

/-! # The native hash-suffix shaper feeds exactly the specified reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem pShape_ok {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (8 * plen - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) (q : Nat) :
    WP isa (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      (∀ a, (∀ i < plen, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rdi, .rsi, .rcx, .rdx, .rax, .r8, .r9, .r10, .r11] s t := by
  obtain ⟨V, R⟩ := hs.rep
  unfold Impl.Dsa.X86_64.Generation.pShape
  refine WP.seq (WP.mono (pShapeArgs_ok hs.layout R hop p.output_slot p.size.2.2 hlmax)
    fun u ⟨hdi, hsi, hcx, hdx, hm, hk⟩ => ?_)
  let rp := off p.output ((p.count + 1) * p.len - plen)
  let bs := Spec.Rsa.bytesAt s.mem rp plen
  have hbl : bs.length = plen := by simp [bs, Spec.Rsa.bytesAt]
  have hrd : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [hbl] at hi
    obtain ⟨r, hr, hc⟩ := hs.outputWrite ((p.count + 1) * p.len - plen + i) (by omega_using [hroom, hi])
    refine ⟨r, ?_, ?_⟩
    · rw [hk.2.1, hk.2.2]; exact List.mem_append_right _ hr
    · simpa only [rp, off_off] using hc
  have hb : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hm]
    simp only [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD]
    simp [show i < plen by omega_using [hbl, hi]]
  refine WP.mono (VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
    (by omega_using [hl] : 9 ≤ 8 * plen) (by omega_using [hlmax]) (by rw [hbl]; omega_using [])
    hsi hdi (by rw [hbl]; exact hcx) hdx hrd
    (fun i hi => by rw [hk.2.2]; exact hout i (hbl ▸ hi)) hb
    (fun i hi j hj => hsep i (hbl ▸ hi) j (hbl ▸ hj)))
    fun t ⟨_, hx, hf, kt⟩ => ?_
  dsimp only
  rw [hbl] at hx
  refine ⟨?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
  · change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) + 1 -
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) % (2 * q) = _
    rw [hx]
    exact hash_shaped_candidate hs (by omega_using [hl]) rfl hroom hcount hhash hsize q
  · change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) % 2 = 1 ∧
      2 ^ (8 * plen - 1) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) < 2 ^ (8 * plen)
    rw [hx]
    exact VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := 8 * plen) (by omega_using [hl]) _
  · intro a ha
    rw [hf a (fun i hi => ha i (hbl ▸ hi)), hm]

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Hash and shape the complete unreduced p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem pBuild_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p H 0 s)
    {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (8 * plen - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j)
    (hbuf : HashBufferSeparate p.F p.S op plen) (q : Nat) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.pHashes G p.len p.count)
      (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen)) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      Lay t p.F p.S ∧ (∃ V, Rep t.mem p.F p.S V p.W) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame (⟨op, plen⟩ :: p.changed) s.mem t.mem := by
  refine WP.seq (WP.mono (pHashes_ok hG hHh hsize hd hs)
    fun u ⟨hu, rdu, wru, csu, hfu⟩ => ?_)
  refine WP.mono (pShape_ok hu hl hlmax hroom hcount hhash hseedsize hop
    (fun i hi => wru ▸ hout i hi) hsep q) fun t ⟨hx, hb, hf, hk⟩ => ?_
  obtain ⟨V, R⟩ := hu.rep
  have Rt := rep_of_external_write R hbuf hf
  refine ⟨hx, hb, lay_of_rep hu.layout R Rt rfl (hk.gpr (by decide)) hk.2.2,
    ⟨V, Rt⟩, hk.2.1.trans rdu, hk.2.2.trans wru, ?_, ?_⟩
  · intro r hr
    have hr' : r ∉ [.rdi, .rsi, .rcx, .rdx, .rax, .r8, .r9, .r10, .r11] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hk.gpr hr').trans (csu r hr)
  · intro a ha
    rw [hf a (fun i hi he => ha ⟨op, plen⟩ (by simp) (he ▸
      Offset.contains_base op (by omega_using [hi]) (by omega_using [hlmax, hi])))]
    exact hfu a (fun r hr => ha r (List.mem_cons_of_mem _ hr))

end VG.Proof.Dsa.X86_64.Generation
