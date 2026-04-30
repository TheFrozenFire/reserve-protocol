#!/usr/bin/env bash
# Run every CAS script under formal-verification/cas/ and surface any FAILs.
#
# Each script is expected to print "OK" / "FAIL" for each invariant it
# probes; this runner greps for FAIL and exits non-zero if any appear.

set -u
cd "$(dirname "$0")"

scripts=(
  fixlib/safe_muldiv_certora_witness.gp
  fixlib/safe_div_propagation.gp
  fixlib/mul_rounding_direction.gp
  fixlib/powu_correctness.gp
  throttle/cap_invariant.gp
  rebalance/basket_range_noise.gp
  rebalance/noise_bound_tightness.gp
  rebalance/basket_range_simulation.gp
  strsr/exchange_rate_evolution.gp
  strsr/withdrawal_queue.gp
  furnace/melt_curve.gp
  distributor/share_conservation.gp
  trade_lib/slippage_sufficiency.gp
  trade_lib/ceil_rounding_witness.gp
  issuance_premium/premium_curve.gp
  dutch_trade/price_decay.gp
  dutch_trade/bid_rounding.gp
  backing_manager/forward_revenue_conservation.gp
  backing_manager/backing_buffer_ceil_witness.gp
  collateral/status_state_machine.gp
  collateral/ref_per_tok_monotonicity.gp
  gnosis_trade/min_buy_amount.gp
  gnosis_trade/settlement_floor.gp
  deprecation/rtoken_deprecation.gp
  basket_handler/quote_rounding_direction.gp
  basket_handler/quote_round_trip.gp
)

failed=0
for s in "${scripts[@]}"; do
  printf "==> %-50s " "$s"
  if [[ ! -f "$s" ]]; then
    echo "MISSING"
    failed=$((failed + 1))
    continue
  fi
  out=$(gp -q < "$s" 2>&1)
  if echo "$out" | grep -qi 'FAIL\|error'; then
    echo "FAIL"
    echo "$out" | sed -n '/FAIL\|error/Ip' | head -5 | sed 's/^/    /'
    failed=$((failed + 1))
  else
    echo "ok"
  fi
done

echo
if [[ $failed -gt 0 ]]; then
  echo "$failed script(s) failed."
  exit 1
else
  echo "All ${#scripts[@]} scripts passed."
fi
