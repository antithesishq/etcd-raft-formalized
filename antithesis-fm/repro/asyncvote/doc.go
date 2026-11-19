// Package asyncvote holds one written schedule for etcd-io/raft with
// AsyncStorageWrites (../../patches/README.md, E1). The test is built only with the
// tag e1, because it fails on raft as it is upstream: run it with
// ../../scripts/e1.sh.
package asyncvote
