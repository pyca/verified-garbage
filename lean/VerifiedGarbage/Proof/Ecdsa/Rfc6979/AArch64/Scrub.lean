module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSpec
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Framework.AArch64.SideFillT
public import VerifiedGarbage.Proof.HmacTable.AArch64.Up
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64.Fn
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.HashTable.First

/-!
# Deterministic ECDSA on AArch64, without secret residue

The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return only
within `out` (`Scrub.ScrubAllOk`, as x86-64's
`Proof/Ecdsa/Rfc6979/X86_64/Scrub.lean` proves it): each implementation,
generic over the HMAC implementations its table holds, which it calls
indirectly, returns with every register it may leave secret cleared and its
whole stack zeroed: the function as emitted is `Impl.Ecdsa.Rfc6979.AArch64.Fn.sign`,
and `sign_scrubbed` is what a curve's theorem comes from.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (HmacUp names tables stubFns fnsOf_up mem_tableFns variants_up)

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [hn, hi]

/-- The postcondition reads the memory on return only within `out`. -/
theorem post_local (T : Spec.Ecdsa.Rfc6979.TableInstance) {A : Abi isa} :
    ∀ vs m m₁ m₂ r, vs.length = (T.signSig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs T.signSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (T.signSig.words A.ptrBits) (fun out d digest _digestLen _scratch hmac m m' r =>
        ∀ H F, Spec.HmacTable.hashAt A.ptrBits m hmac = some H → Spec.HmacTable.hmacOf H = some F →
          match (T.result H F m d digest).1 with
          | some rs => r = 1 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
          | none => r = 0 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 : T.signSig.Post A.ptrBits) vs m m₁ r →
      Curry.apply (T.signSig.words A.ptrBits) (fun out d digest _digestLen _scratch hmac m m' r =>
        ∀ H F, Spec.HmacTable.hashAt A.ptrBits m hmac = some H → Spec.HmacTable.hmacOf H = some F →
          match (T.result H F m d digest).1 with
          | some rs => r = 1 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
          | none => r = 0 ∧ Spec.Sha3.bytesAt m' out (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 : T.signSig.Post A.ptrBits) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [out, d, dg, dl, sc, hm], _ =>
    simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons,
      forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
    have e := bytesAt_of (n := 2 * T.ecdsa.curve.len) (Nat.le_refl _) hb.1
    intro H F h1 h2
    have h' := h H F h1 h2
    revert h'
    split
    · exact fun h' => ⟨h'.1, e.trans h'.2⟩
    · exact fun h' => ⟨h'.1, e.trans h'.2⟩

theorem signOk (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (vs : List MdHash) :
    ScrubAllOk (specK T cs vs) stackT
      (T.signSig.retBits ((abi.withConsts cs).withTables T.signSig [("hmac", tables vs)]).ptrBits) := by
  cases cs with
  | nil =>
    exact scrubAllOk_tables (scrubAllOk_regs (sig := T.signSig) (Nat.le_of_ble_eq_true rfl) (by decide)
      (Nat.le_refl _) (post_local T))
  | cons c₀ cs =>
    exact scrubAllOk_tables (scrubAllOk_consts (sig := T.signSig) (Nat.le_of_ble_eq_true rfl) (by decide)
      (Nat.le_refl _) (post_local T))

/-! ## The function, as emitted -/

open VG.Proof.Variants.MdHash.AArch64 (variants hashes)
open VG.Impl.Ecdsa.Rfc6979.AArch64 (signCode)

/-- The registrations' hash functions of the same name have the same code. -/
theorem variants_coh : HmacTable.AArch64.Coh variants := fun w hw w' hw' =>
  ⟨Proof.HashTable.coh_of_first variants (·.H.hmacInitAnyN) (·.H.hmacInitAny) (by kernel_rfl) w hw w' hw',
    Proof.HashTable.coh_of_first variants (·.H.updN) (·.H.updC) (by kernel_rfl) w hw w' hw',
    Proof.HashTable.coh_of_first variants (·.H.hmacFinN) (·.H.hmacFin) (by kernel_rfl) w hw w' hw'⟩

/-- The hash functions the registrations give meet what the function needs
of them. -/
theorem variants_ok : OK variants := ⟨variants_coh, of_decide_eq_true (by kernel_rfl)⟩

theorem fnsOf_hashes : HmacTable.AArch64.fnsOf variants = Impl.Ecdsa.Rfc6979.AArch64.Fn.fnsOf hashes := by
  kernel_rfl

/-- The code's parameters over stubs of the table's functions. -/
abbrev cfgS (E : Impl.Ecdsa.AArch64.Cfg) (big : Bool) (sh tries : Nat) (coreN : String) (coreC : Prog isa) :
    Impl.Ecdsa.Rfc6979.AArch64.Cfg :=
  { Impl.Ecdsa.Rfc6979.AArch64.Fn.cfg E big sh tries coreN coreC [] with f := stubFns }

theorem sign_tfill (R : RfcCurve) (n : Nat) {vs : List MdHash} (hv : ∀ w ∈ vs, HmacUp w)
    (hk : inames R.coreC = []) :
    TFill 1 (names vs) (signCode (cfgS R.E R.big R.sh n R.coreN R.coreC)) (signCodeT R n vs) := by
  obtain ⟨hI, hU, hF⟩ := fnsOf_up hv
  tfill_calls

/-- `vg_ecdsa_<curve>_sign` on the curve `R` as emitted, cleanup included
(`Impl.Ecdsa.Rfc6979.AArch64.Fn.sign`), with the tables of every hash
function: it meets its contract in constant time and returns without secret
residue. What the cleanup needs of the code is the curve's to evaluate, once,
with nothing in the place of `vg_ecdsa_<curve>_sign_k` and stubs in that of
the table's functions (`hc`, `he`, `hd`), and that function's own (`hk`). -/
theorem sign_scrubbed {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance}
    {cs : List (String × List (BitVec 64))} (hv : Verified target (signCodeT R T.tries variants) (specK T cs variants))
    {n : Nat} (ht8 : T.tries = n)
    (hk : sideAll (fun i => !i.writesDit) R.coreC = true)
    (hc : signCode (cfgS R.E R.big R.sh n R.coreN R.coreC) =
      Code.fill2 (.call R.coreN R.coreC) (.block []) (signCode (cfgS R.E R.big R.sh n "" (.block []))))
    (he : (signCode (cfgS R.E R.big R.sh n "" (.block []))).allInstrs (fun i => !i.writesDit) = true)
    (hd : Code.aarch64Depth2 0 0 (signCode (cfgS R.E R.big R.sh n "" (.block []))) ≤ 40) :
    VerifiedScrubbed target (Impl.Ecdsa.Rfc6979.AArch64.Fn.sign R.E R.big R.sh n R.coreN R.coreC hashes)
      (specK T cs variants) 32 := by
  have ha : (signCode (cfgS R.E R.big R.sh n R.coreN R.coreC)).allInstrs (fun i => !i.writesDit) = true := by
    rw [hc]
    exact allInstrs_fill2 (allInstrs_of_sideAll hk) rfl he
  have hda : (signCode (cfgS R.E R.big R.sh n R.coreN R.coreC)).aarch64Depth ≤ 40 := by
    rw [hc]
    exact Nat.le_trans (Code.aarch64Depth_fill2_le (a := .call R.coreN R.coreC) (b := .block []) (da := 0) (db := 0)
      (Nat.le_of_eq (Proof.Pbkdf2.Md.AArch64.fdepth_of_noFrames R.coreNoFrames)) (Nat.le_refl _) _) hd
  obtain ⟨hdit, htc, hdc⟩ := (sign_tfill R n variants_up (inames_of_noIcall (noIcall_of_sideAll hk))).ok
    (ts := [("hmac", tables variants)]) (fun _ h => mem_tableFns h) ha hda
  have e : signCodeT R n variants =
      signCode (Impl.Ecdsa.Rfc6979.AArch64.Fn.cfg R.E R.big R.sh n R.coreN R.coreC hashes) := by
    rw [signCodeT, cfgT, fnsOf_hashes]
    rfl
  rw [ht8] at hv
  rw [e] at hv hdit htc hdc
  exact verifiedScrubbedOfTA (W := 640) hv (signOk T cs variants) (by decide)
    (Nat.le_trans (Nat.mul_le_mul_left 16 hdc) (by decide)) hdit (fun _ _ h => contract_pub h) htc
    (.inr (.inl rfl))

end VG.Proof.Ecdsa.Rfc6979.AArch64.Scrub
