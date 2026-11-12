# Transaction-envelope finite model check (v1)

This artifact is a finite executable model of transaction-envelope processing. It is **not** the Lean formalization and does **not** prove that a real database, node, or distributed system is linearizable.

## Explicit processing policy

For a request `(request_id, principal, nonce, payload)`:

1. Look up `request_id` before checking the nonce.
2. If the ID already stores the exact same typed payload, return its stored response unchanged. Do not change financial state, nonce, or receipt.
3. If the ID is already bound to a different payload, reject with `REQUEST_ID_CONFLICT` and make no state change.
4. A stale or future nonce is rejected without a receipt. This permits a future-nonce request to be retried after earlier nonces commit.
5. A deterministic authorization rejection is cached under the ID and exact payload, but consumes no nonce and has no financial effect. Repeating it returns that same rejection. A changed authorization context must use a new request ID to attempt the same business payload again.
6. A successful request commits the financial effect, principal nonce increment, and success receipt as one logical state transition.

The model uses exact Python tuple equality for request payload identity. It does not specify canonical byte serialization, a digest, signatures, or threshold authorization.

## Calculated finite cases

- Three distinct requests competing for the same principal nonce: all `3! = 6` arrival orders. Each order has exactly one accepted request and two stale-nonce rejections. Each candidate wins in exactly two orders.
- Four exact retries per winner across those six schedules: 24 replay checks. All return the previously stored response with no state mutation.
- Reuse of the winning request ID with a changed payload: six conflict checks; all are rejected without mutation.
- Three consecutive nonce values delivered in all `3! = 6` orders: eight future-nonce rejections on first pass, then nine total fair retry attempts restore all three accepted operations in every schedule.
- Two principals, two sequential requests each: all six order-preserving cross-principal interleavings accept all four operations and finish with nonce two for each principal.
- Successful commit write set: financial state, principal nonce, success receipt. Of the eight possible component-write subsets, only zero writes and all three writes are all-or-none states; six partial subsets are unsafe.

## Boundaries

The model assumes a serialized atomic transition point. It does not implement or prove mutexes, compare-and-swap, transaction isolation, write-ahead logging, crash durability, consensus ordering, or recovery. The synthetic per-principal balance deltas distinguish winners; they are not the project's holder/GL accounting semantics. The next formal step is a Lean transaction-envelope relation that binds request IDs and exact operation payloads to the existing `ReplayProtectedFinancialStep`, followed by a refinement argument for an executable implementation.
