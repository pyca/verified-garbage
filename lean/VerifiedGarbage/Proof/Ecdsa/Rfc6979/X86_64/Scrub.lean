module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Table
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.TableFill
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out

/-!
# Deterministic ECDSA on x86-64: the postcondition local to the buffers

The postcondition of `vg_ecdsa_<curve>_sign` reads the memory on return
only within `out` (`X86_64.Scrub.PostOut`), for any tables of constants,
tables of `hmac` and stack, as `X86_64.Scrub.withScrubAllUp` needs to scrub
its implementations.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG.X86_64 VG.X86_64.Scrub

/-- `TableInstance.signContract`'s postcondition reads the memory on return
only in `out`. -/
theorem signOut (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64)))
    (ts : List FnTable) (stack : Nat) :
    PostOut (T.signContract ((X86_64.abi.withConsts cs).withTables T.signSig [("hmac", ts)]) stack)
      (T.signSig.retBits ((X86_64.abi.withConsts cs).withTables T.signSig [("hmac", ts)]).ptrBits) :=
  postOut_of_local (leak := some _) ((ScrubAbi.consts cs).tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨hm, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Ecdsa.Rfc6979.TableInstance.signSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
    have e := EcKey.X86_64.Scrub.bytesAt_congr (n := 2 * T.ecdsa.curve.len) (by simp only [Elem.size]; omega)
      hb.1
    intro H F hH hF
    have h := h H F hH hF
    revert h
    split <;> exact fun h => ⟨h.1, e.trans h.2⟩


/-! ## The function as emitted

`vg_ecdsa_<curve>_sign` calls HMAC's functions through its table `hmac`, of
every variant of `Proof.Variants.MdHash.X86_64.variants`; its code has each
variant's code where it calls them (`Code.icalls`). It clears at the level
`sse`, in the baseline ISA, which the AVX code it may run through the table
needs no more of than that its upper halves agree after it
(`X86_64.Scrub.verifiedScrubbedAllUp`). -/

/-- What the cleanup of a caller through a table needs of the HMAC functions
of `w` (`X86_64.Scrub.upCallee`), with 16 bytes of stack. -/
def HmacUp (w : Proof.Pbkdf2.Md.X86_64.MdHash) : Prop :=
  upCallee w.H.hmacInit 16 = true ∧ upCallee w.H.updC 16 = true ∧ upCallee w.H.hmacFin 16 = true

/-- `HmacUp` of every variant, evaluated once for every curve. -/
theorem variants_hmacUp : (VG.Proof.Variants.MdHash.X86_64.variants.all fun w =>
    upCallee w.H.hmacInit 16 && upCallee w.H.updC 16 && upCallee w.H.hmacFin 16) = true := by
  lit_decide


theorem variants_up : ∀ w ∈ VG.Proof.Variants.MdHash.X86_64.variants, HmacUp w := fun w hw => by
  have h := List.all_eq_true.mp variants_hmacUp w hw
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The table's functions, each a stub (`X86_64.Scrub.tableStub`). -/
def stubFns : Impl.Mgf1.X86_64.Table.Fns :=
  ⟨[("t", tableStub 16)], [("t", tableStub 16)], [("t", tableStub 16)]⟩

/-- `cfgT`, with stubs of the table's functions. -/
abbrev cfgS (R : RfcCurve) (tries : Nat) : Impl.Ecdsa.Rfc6979.X86_64.Cfg :=
  { cfgT R tries [] with f := stubFns }

/-- What the cleanup of `vg_ecdsa_<curve>_sign` on the curve `R` needs of its
code with stubs of the table's functions, which the kernel evaluates once for
each curve. -/
def SignStub (R : RfcCurve) (tries : Nat) : Prop :=
  stubUp (Impl.Ecdsa.Rfc6979.X86_64.signCode (cfgS R tries)) 632 = true ∧ UpperLock.inames R.coreC = []

theorem sign_tfill (R : RfcCurve) (tries : Nat) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash)
    (hv : ∀ w ∈ vs, HmacUp w) (hcore : UpperLock.inames R.coreC = []) :
    TFill 16 (Proof.HmacTable.X86_64.names vs) (Impl.Ecdsa.Rfc6979.X86_64.signCode (cfgS R tries))
      (signCodeT R tries vs) := by
  have hI : ∀ q ∈ (Proof.HmacTable.X86_64.fnsOf vs).init,
      upCallee q.2 16 = true ∧ q.1 ∈ Proof.HmacTable.X86_64.names vs := by
    intro q hq; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    exact ⟨(hv w hw).1, (Proof.HmacTable.X86_64.mem_names hw).1⟩
  have hU : ∀ q ∈ (Proof.HmacTable.X86_64.fnsOf vs).upd,
      upCallee q.2 16 = true ∧ q.1 ∈ Proof.HmacTable.X86_64.names vs := by
    intro q hq; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    exact ⟨(hv w hw).2.1, (Proof.HmacTable.X86_64.mem_names hw).2.1⟩
  have hF : ∀ q ∈ (Proof.HmacTable.X86_64.fnsOf vs).fin,
      upCallee q.2 16 = true ∧ q.1 ∈ Proof.HmacTable.X86_64.names vs := by
    intro q hq; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    exact ⟨(hv w hw).2.2, (Proof.HmacTable.X86_64.mem_names hw).2.2⟩
  tfill_calls

/-- `vg_ecdsa_<curve>_sign` on the curve `R`, with the tables of `vs`, as
emitted (`Impl.Ecdsa.Rfc6979.X86_64.Fn.sign`), its cleanup included, meets
its contract in constant time and returns without secret residue, from its
registration's facts `r`, of its code. -/
theorem sign_scrubbed {api : Api} {R : RfcCurve} {tries : Nat} {vs : List Proof.Pbkdf2.Md.X86_64.MdHash}
    (r : Unscrubbed api target) (hpost : PostOut r.contract (retBitsOf r)) (hc : r.code = signCodeT R tries vs)
    (ht : r.tables = [("hmac", Proof.HmacTable.X86_64.tables vs)])
    (hv : ∀ w ∈ vs, HmacUp w) (hs : SignStub R tries)
    (hn : r.stack = 632 := by rfl) (hb : retBitsOf r = 32 := by rfl) :
    VerifiedScrubbed target (Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (cfgT R tries vs)) r.contract 32 := by
  have h := verifiedScrubbedAllUpFill r hpost (hc ▸ sign_tfill R tries vs hv hs.2)
    (fun f hf => by
      rw [ht]
      simp only [Proof.HmacTable.X86_64.names, List.mem_flatten, List.mem_map] at hf
      obtain ⟨l, ⟨a, ha, rfl⟩, hl⟩ := hf
      simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap]
      exact ⟨a, ha, hl⟩) hn hb hs.1 rfl
  rw [hc] at h
  exact h

end VG.Proof.Ecdsa.Rfc6979.X86_64
