pragma solidity ^0.8.0;

import "src/paymaster/ERC20Paymaster.sol";
import "@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol";
import "forge-std/Script.sol";
import "forge-std/console.sol";

//goerli chainlink oracle
//eth/usd: 0xAb5c49580294Aff77670F839ea425f5b78ab3Ae7
//usdc: 0xD4a33860578De61DBAbDc8BFdb98FD742fA7028e

//mumbai oracles
// matic/usd: 0xd0D5e3DB44DE05E9F294BB0a3bEEaF030DE24Ada
// usdc/usd: 0x572dDec9087154dC5dfBB1546Bb62713147e0Ab0

contract DeployERC20Paymaster is Script {
    address constant DEPLOYER = 0x72916f12327309b0c994C77e343F8dBB1A89a617;
    address constant ENTRYPOINT_0_6 = 0x5FF137D4b0FDCD49DcA30c7CF57E578a026d2789;
    function run() public {
        uint256 key = vm.envUint("DEPLOYER_PRIVATE_KEY");
        vm.startBroadcast(key);

        // To deploy new paymaster
        ERC20Paymaster paymaster = new ERC20Paymaster{salt:"0x31"}(
            IERC20Metadata(0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913), //goerli:0x07865c6E87B9F70255377e024ace6630C1Eaa37F , mumbai: 0x9999f7fea5938fd3b1e26a12c3f2fb024e194f97
            IEntryPoint(ENTRYPOINT_0_6), 
            AggregatorV3Interface(0x7e860098F58bBFC8648a4311b374B1D669a2bc6B),  // token oracle
            AggregatorV3Interface(0x71041dddad3595F9CEd3DcCFBe3D1F4b0a16Bb70),  // native oracle
            DEPLOYER
        );
        console.log("erc20 paymaster address: %s", address(paymaster));
        
        // TO update price
        // ERC20Paymaster paymaster = ERC20Paymaster(0x4b1D3D2bbbf209F5994c385032C8f4e949348ADA); //0xA5e19933fAd5C52BE7EDFBAB24BF8C51546d20D0
        // paymaster.updatePrice();
        // console.log("price %s", paymaster.previousPrice()); 

        // To withdraw from paymaster deposit entrypoint
        // paymaster.withdrawTo(payable(0x9fD431b7703f94289Ba02034631dcC302717805B), uint256(250000000000000000));

        vm.stopBroadcast();
    }
}

// forge script scripts/DeployERC20Paymaster.s.sol --chain-id 5 --rpc-url https://goerli.infura.io/v3/087f8478a2174ebd94cc19b9501362a4 --etherscan-api-key 2QTNEVQ2RKXIYS4SGRM8NVCVBB9V1JFWD6  --broadcast
//  forge script scripts/DeployERC20Paymaster.s.sol --chain-id 80001 --rpc-url https://polygon-mumbai.g.alchemy.com/v2/WtsOUcZMFTq2EbOzh2-zRqV9ACPLV7bN --etherscan-api-key 41W6HR54HYPUGD1PQNWRN8NNMXAFGAW6UK  --broadcast