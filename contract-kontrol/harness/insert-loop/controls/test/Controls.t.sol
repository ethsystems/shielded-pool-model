// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Harness_stock} from "../src/Harness_stock.sol";
import {Harness_M1} from "../src/Harness_M1.sol";
import {Harness_M2} from "../src/Harness_M2.sol";
import {Harness_M3} from "../src/Harness_M3.sol";
import {PoseidonT3Stub} from "../src/PoseidonT3Stub.sol";

interface Vm {
    function etch(address, bytes calldata) external;
    function store(address, bytes32, bytes32) external;
    function load(address, bytes32) external view returns (bytes32);
    function deal(address, uint256) external;
    function prank(address) external;
    function readFile(string calldata) external view returns (string memory);
    function parseBytes(string calldata) external pure returns (bytes memory);
    function envOr(string calldata, bool) external view returns (bool);
    function record() external;
    function accesses(address) external returns (bytes32[] memory, bytes32[] memory);
}

contract DelegateEntry {
    fallback() external {
        assembly {
            calldatacopy(0, 0, calldatasize())
            let ok := delegatecall(gas(), 0xa1001, 0, calldatasize(), 0, 0)
            returndatacopy(0, 0, returndatasize())
            if iszero(ok) { revert(0, returndatasize()) }
            return(0, returndatasize())
        }
    }
}

contract ControlsTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address constant POOL = 0xc7183455a4C133Ae270771860664b6B7ec320bB1;
    address constant CALLER = 0x7FA9385bE102ac3EAc297483Dd6233D62b3e1496;
    address constant LIB = address(0xA1001);
    address constant STUB = address(0xA1002);
    uint256 constant F = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    event Observation(string implementation, uint256 mutant, uint256 depth,
        uint256 result, uint256 size, uint256 watched, uint256 wrongSide);

    struct Witness { uint256 depth; uint256 level; uint256 index; uint256 leaf; uint256 node; }

    function setUp() public {
        vm.etch(STUB, _code("stub"));
        vm.deal(POOL, 0);
        vm.deal(CALLER, 0);
        vm.deal(STUB, 0);
    }

    function _code(string memory name) internal view returns (bytes memory) {
        return vm.parseBytes(vm.readFile(string.concat("runtime/", name, ".hex")));
    }

    function _key(uint256 k, uint256 m) internal pure returns (bytes32) { return keccak256(abi.encode(k,m)); }
    function _get(bytes32 k) internal view returns (uint256) { return uint256(vm.load(POOL,k)); }
    function _set(bytes32 k, uint256 v) internal { vm.store(POOL,k,bytes32(v)); }
    function _h(uint256 a, uint256 b) internal pure returns (uint256) { return uint256(keccak256(abi.encode(a,b))) % F; }

    function _w(uint256 depth) internal pure returns (Witness memory w) {
        if (depth == 2) return Witness(2,0,2,11,11);
        require(depth == 4, "unknown witness");
        return Witness(4,1,5,13,13);
    }

    function _seed(Witness memory w) internal {
        _set(bytes32(uint256(0)),9);
        _set(bytes32(uint256(1)),17);
        for (uint256 i; i<=4; ++i) {
            _set(_key(i,2),101+i);
            _set(_key(i,3),701+i);
        }
        _set(_key(w.leaf,2),800+w.leaf);
        _set(_key(w.leaf,3),0);
        _set(bytes32(uint256(77)),177);
        _set(_key(88,105),188);
    }

    function _feasible(Witness memory w, bool post) internal pure {
        require(w.level <= w.depth && w.depth <= 256, "K level/depth");
        require(128+96*(w.depth-w.level)<2**32, "K FMP bound");
        if (post) require(w.index < type(uint256).max, "K post overflow");
        else require(((w.index >> w.level)&1)==0, "witness zero bit");
        // A5=0, SELF=0. Frame2 has K=initial LEVEL, M=3, WS empty.
        // Frame/exact instead have WS=[initial LEVEL,3]. Post has WS empty.
        require(w.leaf != 0 && w.leaf < F, "canonical leaf (extra restriction)");
    }

    function _install(uint256 mutant, bool raw, bool post) internal {
        bool negative=vm.envOr("LOOP_MUTANTS",false);
        string memory tag=negative ? (mutant==1 ? "M1" : mutant==2 ? "M2" : "M3") : "stock";
        if (raw) {
            vm.etch(LIB,_code(string.concat(tag,post ? "-post" : "-loop")));
            vm.etch(POOL,type(DelegateEntry).runtimeCode);
        } else if (!negative) vm.etch(POOL,type(Harness_stock).runtimeCode);
        else if (mutant==1) vm.etch(POOL,type(Harness_M1).runtimeCode);
        else if (mutant==2) vm.etch(POOL,type(Harness_M2).runtimeCode);
        else vm.etch(POOL,type(Harness_M3).runtimeCode);
    }

    function _call(bytes memory data) internal returns (bytes memory output) {
        vm.prank(CALLER);
        (bool ok,bytes memory result)=POOL.call(data);
        require(ok,"segment reverted before postcondition");
        return result;
    }

    function _expectedNode(Witness memory w) internal pure returns (uint256 n) {
        n=w.node;
        for (uint256 l=w.level;l<w.depth;++l) if ((w.index>>l)&1==1) n=_h(101+l,n);
    }

    function _loop(Witness memory w, uint256 mutant, bool raw) internal {
        _feasible(w,false);
        _install(mutant % 10,raw,false);
        _seed(w);
        vm.record();
        bytes memory output;
        if (raw) output=_call(abi.encode(w.level,w.node,w.depth,w.index,uint256(0),w.leaf,uint256(0),w.level,uint256(3)));
        else output=_call(abi.encodeCall(Harness_stock.runLoop,(w.level,w.depth,w.index,w.node)));
        (,bytes32[] memory writes)=vm.accesses(POOL);
        (uint256 level,uint256 node)=abi.decode(output,(uint256,uint256));
        _observe(w, mutant, raw, node, false);
        require(level==w.depth,"loop level does not reach DEPTH");
        if (raw) {
            uint256[9] memory words=abi.decode(output,(uint256[9]));
            require(words[2]==w.depth && words[3]==w.index && words[4]==0 && words[5]==w.leaf && words[6]==0 && words[7]==w.level && words[8]==3,"K stack frame changed");
        }
        // Assert the unchanged positive claim, including in negative runs.
        if (mutant==1) require(_get(0)==9,"loop-frame: slot 0 changed");
        if (mutant==2) require(_get(_key(w.level,3))==701+w.level,"loop-frame2: watched leaves key changed");
        if (mutant < 10) {
            require(_get(0)==9 && _get(bytes32(uint256(1)))==17,"loop-frame: size/depth changed");
            require(_get(_key(w.level,3))==701+w.level,"loop-frame2: watched leaves key changed");
        }
        require(node==_expectedNode(w),"loop-exact: node mismatch");
        uint256 n=w.node;
        for (uint256 l; l<=4; ++l) {
            uint256 expected=101+l;
            if (l>=w.level && l<w.depth) {
                if ((w.index>>l)&1==1) n=_h(101+l,n);
                else expected=n;
            }
            require(_get(_key(l,2))==expected,"loop-exact: sideNodes mismatch");
            require(_get(_key(l,3))==701+l,"loop-exact: leaves mismatch");
        }
        // Complete concrete write footprint: any write outside a visited zero-bit key fails.
        for (uint256 j; j<writes.length; ++j) {
            bool allowed;
            for (uint256 l=w.level;l<w.depth;++l) if ((w.index>>l)&1==0 && writes[j]==_key(l,2)) allowed=true;
            require(allowed,"loop-exact: unexpected storage write");
        }
        _sentinels(w);
    }

    function _post(Witness memory w, bool raw) internal {
        _feasible(w,true);
        _install(3,raw,true);
        _seed(w);
        uint256 node=_expectedNode(w);
        vm.record();
        bytes memory output;
        if (raw) output=_call(abi.encode(w.depth,node,w.depth,w.index,uint256(0),w.leaf,uint256(0),uint256(369)));
        else output=_call(abi.encodeCall(Harness_stock.runPost,(w.depth,w.index,node,w.leaf)));
        (,bytes32[] memory writes)=vm.accesses(POOL);
        uint256 ret=abi.decode(output,(uint256));
        _observe(w, 3, raw, ret, true);
        require(ret==node,"post-loop-exact: return mismatch");
        require(_get(0)==w.index+1,"post-loop-exact: INDEX+1 mismatch");
        require(_get(_key(w.depth,2))==node,"post-loop-exact: root mismatch");
        require(_get(_key(w.leaf,3))==w.index+1,"post-loop-exact: leaves[LEAF] missing");
        for (uint256 j; j<writes.length; ++j) require(writes[j]==0 || writes[j]==_key(w.depth,2) || writes[j]==_key(w.leaf,3),"post-loop-exact: unexpected storage write");
        for (uint256 l; l<=4; ++l) {
            require(_get(_key(l,2))==(l==w.depth ? node : 101+l),"post-loop-exact: sideNodes mismatch");
            require(_get(_key(l,3))==701+l,"post-loop-exact: other leaves changed");
        }
        require(_get(bytes32(uint256(1)))==17,"post-loop-exact: stored depth changed");
        _sentinels(w);
    }

    function _observe(Witness memory w, uint256 mutant, bool raw, uint256 node, bool post) internal {
        emit Observation(raw ? "archived runtime" : "source",mutant,w.depth,node,_get(0),
            _get(_key(post ? w.leaf : w.level,3)),_get(_key(w.leaf,2)));
    }

    function _sentinels(Witness memory w) internal view {
        require(_get(_key(w.leaf,2))==800+w.leaf,"unexpected sideNodes[LEAF] change");
        require(_get(bytes32(uint256(77)))==177 && _get(_key(88,105))==188,"unrelated storage changed");
    }

    function test_source_M1_depth2() public { _loop(_w(2),1,false); }
    function test_source_M1_depth4() public { _loop(_w(4),1,false); }
    function test_source_M2_depth2() public { _loop(_w(2),2,false); }
    function test_source_M2_depth4() public { _loop(_w(4),2,false); }
    function test_source_M3_depth2() public { _post(_w(2),false); }
    function test_source_M3_depth4() public { _post(_w(4),false); }
    function test_runtime_M1_depth2() public { _loop(_w(2),1,true); }
    function test_runtime_M1_depth4() public { _loop(_w(4),1,true); }
    function test_runtime_M2_depth2() public { _loop(_w(2),2,true); }
    function test_runtime_M2_depth4() public { _loop(_w(4),2,true); }
    function test_runtime_M3_depth2() public { _post(_w(2),true); }
    function test_runtime_M3_depth4() public { _post(_w(4),true); }

    function test_source_exact_M1_depth2() public { _loop(_w(2),11,false); }
    function test_source_exact_M1_depth4() public { _loop(_w(4),11,false); }
    function test_source_exact_M2_depth2() public { _loop(_w(2),12,false); }
    function test_source_exact_M2_depth4() public { _loop(_w(4),12,false); }
    function test_runtime_exact_M1_depth2() public { _loop(_w(2),11,true); }
    function test_runtime_exact_M1_depth4() public { _loop(_w(4),11,true); }
    function test_runtime_exact_M2_depth2() public { _loop(_w(2),12,true); }
    function test_runtime_exact_M2_depth4() public { _loop(_w(4),12,true); }

    function test_stub_matches_archived_runtime() public {
        PoseidonT3Stub sourceStub=new PoseidonT3Stub();
        for (uint256 i; i<2; ++i) {
            uint256[2] memory x=i==0 ? [uint256(102),uint256(11)] : [uint256(103),uint256(13)];
            (bool ok,bytes memory out)=STUB.staticcall(abi.encodeCall(PoseidonT3Stub.hash,(x)));
            require(ok && abi.decode(out,(uint256))==sourceStub.hash(x),"stub source/runtime mismatch");
        }
    }
}
