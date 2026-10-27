// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
interface VM {
    function etch(address, bytes calldata) external;
    function assume(bool) external;
    function load(address, bytes32) external view returns (bytes32);
}
interface SVM {
    function enableSymbolicStorage(address) external;
    function snapshotState() external returns (bytes32);
}
abstract contract FrameBase {
    VM internal constant vm = VM(address(uint160(uint256(keccak256("hevm cheat code")))));
    SVM internal constant svm = SVM(address(uint160(uint256(keccak256("svm cheat code")))));
    address internal constant LIB = address(0xA1002);
    bytes4 internal constant HASH = 0x561558fe;

    function check_frame_equal_inputs(uint256 x, uint256 y, bytes32 slot) public {
        bytes memory data = abi.encodeWithSelector(HASH, x, y);
        bytes32 beforeSlot = vm.load(address(this), slot);
        bytes32 beforeState = svm.snapshotState();
        (bool ok1, bytes memory a) = LIB.delegatecall(data);
        assert(ok1);
        assert(a.length == 32);
        assert(svm.snapshotState() == beforeState);
        assert(vm.load(address(this), slot) == beforeSlot);
        (bool ok2, bytes memory b) = LIB.delegatecall(data);
        assert(ok2);
        assert(b.length == 32);
        assert(abi.decode(a, (uint256)) == abi.decode(b, (uint256)));
        assert(svm.snapshotState() == beforeState);
    }

    function check_call_context_same_result(uint256 x, uint256 y) public {
        bytes memory data = abi.encodeWithSelector(HASH, x, y);
        bytes32 beforeState = svm.snapshotState();
        (bool directOk, bytes memory direct) = LIB.call(data);
        assert(directOk && direct.length == 32);
        assert(svm.snapshotState() == beforeState);
        (bool delegateOk, bytes memory delegated) = LIB.delegatecall(data);
        assert(delegateOk && delegated.length == 32);
        assert(abi.decode(direct, (uint256)) == abi.decode(delegated, (uint256)));
        assert(svm.snapshotState() == beforeState);
    }

    function check_wrong_selector(bytes4 selector, uint256 x, uint256 y) public {
        vm.assume(selector != HASH);
        bytes32 beforeState = svm.snapshotState();
        (bool ok, bytes memory ret) = LIB.delegatecall(abi.encodeWithSelector(selector, x, y));
        assert(!ok && ret.length == 0);
        assert(svm.snapshotState() == beforeState);
    }

    function check_short_calldata(bytes memory data) public {
        vm.assume(data.length < 68);
        bytes32 beforeState = svm.snapshotState();
        (bool ok, bytes memory ret) = LIB.delegatecall(data);
        assert(!ok && ret.length == 0);
        assert(svm.snapshotState() == beforeState);
    }
}
