# OIP v0.6.1 validation inputs

The input manifest records the byte count and SHA-256 of each synthetic input and driver. The versioned OIP source repository supplies the wire operation corpus, the state commitment structure fixtures, and the Write execution vectors.

| Input | Isabelle export session | Observation |
| --- | --- | --- |
| `sync/product-input.ML` | `OIP_Sync_V061_Product_ABI` | Selected stream, exact outcome, current cut, query and receipt behavior |
| `sync/fresh-modes-input.ML` | `OIP_Sync_V061_Mode_Product_ABI` | A fresh step from the supplied current projection for each input |
| `sync/configured-profile-input.ML` | `OIP_Sync_V061_Configured_Profile_ABI` | Refusal order in the earlier decoder, the configured receiver and the signature control |
| `sync/id-guards-input.ML` | `OIP_Sync_V061_ID_Guard_ABI_V2` | Existing caller ID and ordered reservation checks after transport admission |
| `sync/image-binding-input.ML` | `OIP_Sync_V061_Image_Binding_ABI` | Exact Core and transport map before and after removing one entry |
| `response/ack-input.ML` | `OIP_Sync_V061_Ack_ABI` | Raw operand correlation and signed response verification |
| `supplier/input.ML` | `OIP_Sync_V061_Supplier_ABI` | Assembly from the selected source votes and replay against the authenticated prefix |
| `current-read/packet.tsv` and `current-read/inputs.tsv` | `OIP_Current_Read_Vector_Export` | Current value, stale cut, exact session permission and selected head |
| `write/raw-ack.jsonl` | `OIP_Reference_Write_Raw_Ack_Seed` | Exact Write original, response code 20 and commit position zero at the raw operand boundary |
| `write/max-version.hex` and `write/capacity-observation.tsv` | `OIP_Reference_Write_Capacity` | Write at an artificial ledger boundary with the asset version already at its upper bound |

Extract the named session's code export with Isabelle. Use the supplied input-only ML files with `drivers/trace.ML` for product, mode, configured profile, image and ACK observations. The driver reads the generated model through `OIP_SYNC_PRODUCT_MODEL` and the input through `OIP_SYNC_PRODUCT_INPUT`. The supplier and ID guard drivers use the variables documented in their sources.

The product inputs describe the selected state and authorization context supplied to the model. The mode inputs supply the current projection of each independent step. The supplier inputs supply authenticated records and the votes already issued from the selected source. The raw Write ACK contains placeholder signature octets for the operand decoder.
