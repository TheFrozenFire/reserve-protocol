(** Distributor simulation × CAS witness cross-check.

    Evaluates the [Distributor] simulation on the same calibration inputs
    used by [cas/distributor/share_conservation.gp] and asserts identical
    outputs. Any divergence between the Rocq simulation and the CAS
    witness corpus fails the build.

    Concrete probes (matching the CAS script):
      - $1M evenly to 4 dests, even shares  (amount=10^24, shares=[25,25,25,25])
      - $1M to Furnace+StRSR (4000/6000)    (amount=10^24, shares=[4000,6000])
      - $1M with prime-factor share total   (amount=10^24, shares=[3,7,11,13])
      - $1 (1 wei rounded down)             (amount=1,    shares=[4000,6000])
      - prime-amount, prime-shares          (amount=1000003, shares=[1,2])
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Reserve.simulations.Distributor.
Require Import Coq.Lists.List.
Import ListNotations.

Module DistributorXCheck.

Import Distributor.

(** Helpers — RToken-side share, and a destination address. *)
Definition rtok (r : Z) : RevenueShare.t :=
  {| RevenueShare.rTokenDist := r; RevenueShare.rsrDist := 0 |}.

Definition dest (i : Z) : U256.t := i.

(** ---------- Probe 1: $1M evenly to 4 dests, shares=[25,25,25,25]. ----------
    totalShares = 100, tps = 10^24 / 100 = 10^22, each transfer = 10^22 * 25 = 25 * 10^22.
    paidOut = 4 * 25 * 10^22 = 10^24, dust = 0. *)
Definition probe1_storage : Storage :=
  [(dest 1, rtok 25); (dest 2, rtok 25); (dest 3, rtok 25); (dest 4, rtok 25)].

Lemma xcheck_probe1 :
  distributeAmounts probe1_storage (10^24) false
  = ([25 * 10^22; 25 * 10^22; 25 * 10^22; 25 * 10^22], 0).
Proof. vm_compute. reflexivity. Qed.

(** ---------- Probe 2: $1M to Furnace+StRSR (4000/6000). ----------
    totalShares = 10000, tps = 10^24 / 10000 = 10^20.
    transfers = [4000*10^20; 6000*10^20] = [4*10^23; 6*10^23]; dust = 0. *)
Definition probe2_storage : Storage :=
  [(dest 1, rtok 4000); (dest 2, rtok 6000)].

Lemma xcheck_probe2 :
  distributeAmounts probe2_storage (10^24) false
  = ([4 * 10^23; 6 * 10^23], 0).
Proof. vm_compute. reflexivity. Qed.

(** ---------- Probe 3: $1M with prime-factor shares=[3,7,11,13]. ----------
    totalShares = 34, tps = 10^24 \ 34 (floor).
    Verified per CAS: dust = 10^24 mod 34. *)
Definition probe3_storage : Storage :=
  [(dest 1, rtok 3); (dest 2, rtok 7); (dest 3, rtok 11); (dest 4, rtok 13)].

Lemma xcheck_probe3_dust :
  snd (distributeAmounts probe3_storage (10^24) false) = (10^24) mod 34.
Proof. vm_compute. reflexivity. Qed.

(** ---------- Probe 4: 1 wei against shares [4000,6000]. ----------
    totalShares = 10000, tps = 1/10000 = 0 (floor).
    transfers = [0;0], dust = 1. (CAS reports dust=1, sum_transfers=0.) *)
Lemma xcheck_probe4 :
  distributeAmounts probe2_storage 1 false = ([0; 0], 1).
Proof. vm_compute. reflexivity. Qed.

(** ---------- Probe 5: amount=1000003, shares=[1,2]. ----------
    totalShares=3, tps=1000003/3=333334 (floor),
    transfers=[333334; 666668], paidOut=1000002, dust=1=1000003 mod 3.
    CAS: "totalShares=3, dust=1000003%3=1". *)
Definition probe5_storage : Storage :=
  [(dest 1, rtok 1); (dest 2, rtok 2)].

Lemma xcheck_probe5 :
  distributeAmounts probe5_storage 1000003 false
  = ([333334; 666668], 1).
Proof. vm_compute. reflexivity. Qed.

(** ---------- Bonus: totals on probe2 (4000+6000 = 10000). ---------- *)
Lemma xcheck_probe2_totals :
  totals probe2_storage = (10000, 0).
Proof. vm_compute. reflexivity. Qed.

End DistributorXCheck.
