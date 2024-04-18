/* Autogenerated file. Do not edit manually. */
/* tslint:disable */
/* eslint-disable */
import { Signer, utils, Contract, ContractFactory, Overrides } from "ethers";
import type { Provider, TransactionRequest } from "@ethersproject/providers";
import type { PromiseOrValue } from "../common";
import type { Kernel, KernelInterface } from "../Kernel";

const _abi = [
  {
    inputs: [
      {
        internalType: "contract IEntryPoint",
        name: "_entryPoint",
        type: "address",
      },
    ],
    stateMutability: "nonpayable",
    type: "constructor",
  },
  {
    inputs: [],
    name: "AlreadyInitialized",
    type: "error",
  },
  {
    inputs: [],
    name: "DisabledMode",
    type: "error",
  },
  {
    inputs: [],
    name: "NotAuthorizedCaller",
    type: "error",
  },
  {
    inputs: [],
    name: "NotEntryPoint",
    type: "error",
  },
  {
    anonymous: false,
    inputs: [
      {
        indexed: true,
        internalType: "address",
        name: "oldValidator",
        type: "address",
      },
      {
        indexed: true,
        internalType: "address",
        name: "newValidator",
        type: "address",
      },
    ],
    name: "DefaultValidatorChanged",
    type: "event",
  },
  {
    anonymous: false,
    inputs: [
      {
        indexed: true,
        internalType: "bytes4",
        name: "selector",
        type: "bytes4",
      },
      {
        indexed: true,
        internalType: "address",
        name: "executor",
        type: "address",
      },
      {
        indexed: true,
        internalType: "address",
        name: "validator",
        type: "address",
      },
    ],
    name: "ExecutionChanged",
    type: "event",
  },
  {
    anonymous: false,
    inputs: [
      {
        indexed: true,
        internalType: "address",
        name: "newImplementation",
        type: "address",
      },
    ],
    name: "Upgraded",
    type: "event",
  },
  {
    stateMutability: "payable",
    type: "fallback",
  },
  {
    inputs: [
      {
        internalType: "bytes4",
        name: "_disableFlag",
        type: "bytes4",
      },
    ],
    name: "disableMode",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [],
    name: "eip712Domain",
    outputs: [
      {
        internalType: "bytes1",
        name: "fields",
        type: "bytes1",
      },
      {
        internalType: "string",
        name: "name",
        type: "string",
      },
      {
        internalType: "string",
        name: "version",
        type: "string",
      },
      {
        internalType: "uint256",
        name: "chainId",
        type: "uint256",
      },
      {
        internalType: "address",
        name: "verifyingContract",
        type: "address",
      },
      {
        internalType: "bytes32",
        name: "salt",
        type: "bytes32",
      },
      {
        internalType: "uint256[]",
        name: "extensions",
        type: "uint256[]",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "entryPoint",
    outputs: [
      {
        internalType: "contract IEntryPoint",
        name: "",
        type: "address",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "to",
        type: "address",
      },
      {
        internalType: "uint256",
        name: "value",
        type: "uint256",
      },
      {
        internalType: "bytes",
        name: "data",
        type: "bytes",
      },
      {
        internalType: "enum Operation",
        name: "operation",
        type: "uint8",
      },
    ],
    name: "execute",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address[]",
        name: "dest",
        type: "address[]",
      },
      {
        internalType: "uint256[]",
        name: "values",
        type: "uint256[]",
      },
      {
        internalType: "bytes[]",
        name: "func",
        type: "bytes[]",
      },
      {
        internalType: "enum Operation",
        name: "operation",
        type: "uint8",
      },
    ],
    name: "executeBatch",
    outputs: [],
    stateMutability: "nonpayable",
    type: "function",
  },
  {
    inputs: [],
    name: "getDefaultValidator",
    outputs: [
      {
        internalType: "contract IKernelValidator",
        name: "validator",
        type: "address",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "getDisabledMode",
    outputs: [
      {
        internalType: "bytes4",
        name: "disabled",
        type: "bytes4",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "bytes4",
        name: "_selector",
        type: "bytes4",
      },
    ],
    name: "getExecution",
    outputs: [
      {
        components: [
          {
            internalType: "ValidAfter",
            name: "validAfter",
            type: "uint48",
          },
          {
            internalType: "ValidUntil",
            name: "validUntil",
            type: "uint48",
          },
          {
            internalType: "address",
            name: "executor",
            type: "address",
          },
          {
            internalType: "contract IKernelValidator",
            name: "validator",
            type: "address",
          },
        ],
        internalType: "struct ExecutionDetail",
        name: "",
        type: "tuple",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "getLastDisabledTime",
    outputs: [
      {
        internalType: "uint48",
        name: "",
        type: "uint48",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "uint192",
        name: "key",
        type: "uint192",
      },
    ],
    name: "getNonce",
    outputs: [
      {
        internalType: "uint256",
        name: "",
        type: "uint256",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "getNonce",
    outputs: [
      {
        internalType: "uint256",
        name: "",
        type: "uint256",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "contract IKernelValidator",
        name: "_defaultValidator",
        type: "address",
      },
      {
        internalType: "bytes",
        name: "_data",
        type: "bytes",
      },
    ],
    name: "initialize",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "bytes32",
        name: "hash",
        type: "bytes32",
      },
      {
        internalType: "bytes",
        name: "signature",
        type: "bytes",
      },
    ],
    name: "isValidSignature",
    outputs: [
      {
        internalType: "bytes4",
        name: "",
        type: "bytes4",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "name",
    outputs: [
      {
        internalType: "string",
        name: "",
        type: "string",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "",
        type: "address",
      },
      {
        internalType: "address",
        name: "",
        type: "address",
      },
      {
        internalType: "uint256[]",
        name: "",
        type: "uint256[]",
      },
      {
        internalType: "uint256[]",
        name: "",
        type: "uint256[]",
      },
      {
        internalType: "bytes",
        name: "",
        type: "bytes",
      },
    ],
    name: "onERC1155BatchReceived",
    outputs: [
      {
        internalType: "bytes4",
        name: "",
        type: "bytes4",
      },
    ],
    stateMutability: "pure",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "",
        type: "address",
      },
      {
        internalType: "address",
        name: "",
        type: "address",
      },
      {
        internalType: "uint256",
        name: "",
        type: "uint256",
      },
      {
        internalType: "uint256",
        name: "",
        type: "uint256",
      },
      {
        internalType: "bytes",
        name: "",
        type: "bytes",
      },
    ],
    name: "onERC1155Received",
    outputs: [
      {
        internalType: "bytes4",
        name: "",
        type: "bytes4",
      },
    ],
    stateMutability: "pure",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "",
        type: "address",
      },
      {
        internalType: "address",
        name: "",
        type: "address",
      },
      {
        internalType: "uint256",
        name: "",
        type: "uint256",
      },
      {
        internalType: "bytes",
        name: "",
        type: "bytes",
      },
    ],
    name: "onERC721Received",
    outputs: [
      {
        internalType: "bytes4",
        name: "",
        type: "bytes4",
      },
    ],
    stateMutability: "pure",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "contract IKernelValidator",
        name: "_defaultValidator",
        type: "address",
      },
      {
        internalType: "bytes",
        name: "_data",
        type: "bytes",
      },
    ],
    name: "setDefaultValidator",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "bytes4",
        name: "_selector",
        type: "bytes4",
      },
      {
        internalType: "address",
        name: "_executor",
        type: "address",
      },
      {
        internalType: "contract IKernelValidator",
        name: "_validator",
        type: "address",
      },
      {
        internalType: "uint48",
        name: "_validUntil",
        type: "uint48",
      },
      {
        internalType: "uint48",
        name: "_validAfter",
        type: "uint48",
      },
      {
        internalType: "bytes",
        name: "_enableData",
        type: "bytes",
      },
    ],
    name: "setExecution",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "_newImplementation",
        type: "address",
      },
    ],
    name: "upgradeTo",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        components: [
          {
            internalType: "address",
            name: "sender",
            type: "address",
          },
          {
            internalType: "uint256",
            name: "nonce",
            type: "uint256",
          },
          {
            internalType: "bytes",
            name: "initCode",
            type: "bytes",
          },
          {
            internalType: "bytes",
            name: "callData",
            type: "bytes",
          },
          {
            internalType: "uint256",
            name: "callGasLimit",
            type: "uint256",
          },
          {
            internalType: "uint256",
            name: "verificationGasLimit",
            type: "uint256",
          },
          {
            internalType: "uint256",
            name: "preVerificationGas",
            type: "uint256",
          },
          {
            internalType: "uint256",
            name: "maxFeePerGas",
            type: "uint256",
          },
          {
            internalType: "uint256",
            name: "maxPriorityFeePerGas",
            type: "uint256",
          },
          {
            internalType: "bytes",
            name: "paymasterAndData",
            type: "bytes",
          },
          {
            internalType: "bytes",
            name: "signature",
            type: "bytes",
          },
        ],
        internalType: "struct UserOperation",
        name: "userOp",
        type: "tuple",
      },
      {
        internalType: "bytes32",
        name: "userOpHash",
        type: "bytes32",
      },
      {
        internalType: "uint256",
        name: "missingAccountFunds",
        type: "uint256",
      },
    ],
    name: "validateUserOp",
    outputs: [
      {
        internalType: "ValidationData",
        name: "validationData",
        type: "uint256",
      },
    ],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [],
    name: "version",
    outputs: [
      {
        internalType: "string",
        name: "",
        type: "string",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    stateMutability: "payable",
    type: "receive",
  },
] as const;

const _bytecode =
  "0x61014034620001b757601f6200230b38819003918201601f19168301916001600160401b03831184841017620001bc57808492602094604052833981010312620001b757516001600160a01b0381168103620001b757306080524660a05260a062000069620001d2565b600681526005602082016512d95c9b995b60d21b815260206200008b620001d2565b838152019264302e322e3160d81b845251902091208160c0528060e052604051917f8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f83526020830152604082015246606082015230608082015220906101009182526101209081527f439ffe7df606b78489639bc0b827913bd09e1246fa6802968a5b3694c53e0dd96a010000000000000000000080600160f01b0319825416179055604051906121189283620001f3843960805183611c0c015260a05183611c2f015260c05183611ca1015260e05183611cc701525182611beb0152518181816104ad01528181610664015281816108bd01528181610a5301528181610b7a01528181610f380152818161105901528181611158015281816112820152818161135401526116050152f35b600080fd5b634e487b7160e01b600052604160045260246000fd5b60408051919082016001600160401b03811183821017620001bc5760405256fe60806040526004361015610015575b3661126557005b60003560e01c806306fdde03146101755780630b3dc35414610170578063150b7a021461016b5780631626ba7e1461016657806329f8b174146101615780633659cfe61461015c5780633a871cdd146101575780633e1b08121461015257806351166ba01461014d578063519454471461014857806354fd4d501461014357806355b14f501461013e57806357b750471461013957806384b0196e1461013457806388e7fd061461012f578063a4c79eee1461012a578063b0d691fe14610125578063bc197c8114610120578063d087d2881461011b578063d1f5789414610116578063d5416221146101115763f23a6e610361000e576111d3565b611141565b6110a5565b611026565b610f97565b610f22565b610e53565b610d29565b610c81565b610c4a565b610b64565b610b0c565b610a10565b610938565b610874565b61074a565b610640565b61043f565b6103ad565b610353565b6102d4565b6102a0565b600091031261018557565b600080fd5b634e487b7160e01b600052604160045260246000fd5b6001600160401b0381116101b357604052565b61018a565b608081019081106001600160401b038211176101b357604052565b604081019081106001600160401b038211176101b357604052565b90601f801991011681019081106001600160401b038211176101b357604052565b6040519061021c826101b8565b565b6040519061016082018281106001600160401b038211176101b357604052565b6040519061024b826101d3565b600682526512d95c9b995b60d21b6020830152565b919082519283825260005b84811061028c575050826000602080949584010152601f8019910116010190565b60208183018101518483018201520161026b565b34610185576000366003190112610185576102d06102bc61023e565b604051918291602083526020830190610260565b0390f35b346101855760003660031901126101855760206000805160206120f88339815191525460501c6040519060018060a01b03168152f35b6001600160a01b0381160361018557565b359061021c8261030a565b9181601f84011215610185578235916001600160401b038311610185576020838186019501011161018557565b346101855760803660031901126101855761036f60043561030a565b61037a60243561030a565b6064356001600160401b03811161018557610399903690600401610326565b5050604051630a85bd0160e11b8152602090f35b34610185576040366003190112610185576024356001600160401b038111610185576103eb6103e26020923690600401610326565b90600435611cfd565b6040516001600160e01b03199091168152f35b600435906001600160e01b03198216820361018557565b6064359065ffffffffffff8216820361018557565b6084359065ffffffffffff8216820361018557565b60c0366003190112610185576104536103fe565b602435906104608261030a565b6044359061046d8261030a565b610475610415565b9261047e61042a565b9060a4356001600160401b0381116101855761049e903690600401610326565b9590946001600160a01b0393337f00000000000000000000000000000000000000000000000000000000000000008616141580610636575b610624578492610500610597926104eb61020f565b65ffffffffffff918216815292166020830152565b6001600160a01b03851660408201526001600160a01b03831660608201526105278761122d565b81516020830151604084015160309190911b6bffffffffffff0000000000001665ffffffffffff9290921691909117606091821b6bffffffffffffffffffffffff19161782559091015160019190910180546001600160a01b0319166001600160a01b0392909216919091179055565b1693843b15610185576040519063064acaab60e11b825281806105c16000998a94600484016118fd565b038183895af1801561061f57610606575b5016906001600160e01b0319167fed03d2572564284398470d3f266a693e29ddfff3eba45fc06c5e91013d3213538480a480f35b80610613610619926101a0565b8061017a565b386105d2565b6115e5565b604051637046c88d60e01b8152600490fd5b50303314156104d6565b6020366003190112610185576004356106588161030a565b6001600160a01b0390337f000000000000000000000000000000000000000000000000000000000000000083161415806106dc575b61062457807f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc55167fbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b600080a2005b503033141561068d565b9291926001600160401b0382116101b3576040519161070f601f8201601f1916602001846101ee565b829481845281830111610185578281602093846000960137010152565b9080601f8301121561018557816020610747933591016106e6565b90565b6003196060368201126101855760048035916001600160401b0390818411610185576101609084360301126101855761078161021e565b9061078d84840161031b565b8252602484013560208301526044840135818111610185576107b49084369187010161072c565b60408301526064840135818111610185576107d49084369187010161072c565b60608301526084840135608083015260a484013560a083015260c484013560c083015260e484013560e0830152610104840135610100830152610124840135818111610185576108299084369187010161072c565b610120830152610144840135908111610185576102d09361086493610851923692010161072c565b61014082015260443590602435906115f1565b6040519081529081906020820190565b34610185576020366003190112610185576004356001600160c01b0381169081900361018557604051631aab3f0d60e11b815230600482015260248101919091526020816044817f00000000000000000000000000000000000000000000000000000000000000006001600160a01b03165afa801561061f576102d09160009161090a575b506040519081529081906020820190565b61092b915060203d8111610931575b61092381836101ee565b810190611506565b386108f9565b503d610919565b34610185576020366003190112610185576102d061097d6109576103fe565b60006060604051610967816101b8565b828152826020820152826040820152015261122d565b6040519061098a826101b8565b805465ffffffffffff80821684528160301c16602084015260601c60408301526001808060a01b03910154166060820152604051918291829190916060608082019365ffffffffffff80825116845260208201511660208401528160018060a01b0391826040820151166040860152015116910152565b60643590600282101561018557565b608036600319011261018557600435610a288161030a565b6044356001600160401b03811161018557610a4790369060040161072c565b90610a50610a01565b337f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316141580610ad6575b61062457610a90816112de565b610ab9576000828193926020839451920190602435905af13d82803e15610ab5573d90f35b3d90fd5b60008281939260208394519201905af43d82803e15610ab5573d90f35b50610ae6610ae2611e30565b1590565b610a83565b60405190610af8826101d3565b6005825264302e322e3160d81b6020830152565b34610185576000366003190112610185576102d06102bc610aeb565b90604060031983011261018557600435610b418161030a565b91602435906001600160401b03821161018557610b6091600401610326565b9091565b610b6d36610b28565b90916001600160a01b03337f00000000000000000000000000000000000000000000000000000000000000008216141580610c40575b61062457806000805160206120f88339815191525460501c1691610bc681611fc6565b1692836040519360009586947fa35f5cdc5fbabb614b4cd5064ce5543f43dc8fab0e4da41255230eb8aba2531c8680a3813b15610c3c578385610c1a819593829463064acaab60e11b8452600484016118fd565b03925af1801561061f57610c2c575080f35b80610613610c39926101a0565b80f35b8380fd5b5030331415610ba3565b346101855760003660031901126101855760206000805160206120f88339815191525460e01b6040519063ffffffff60e01b168152f35b3461018557600036600319011261018557610cd7610c9d61023e565b610ca5610aeb565b90604051928392600f60f81b8452610cc960209360e08587015260e0860190610260565b908482036040860152610260565b90466060840152306080840152600060a084015282820360c08401528060605192838152019160809160005b828110610d1257505050500390f35b835185528695509381019392810192600101610d03565b346101855760003660031901126101855760206000805160206120f88339815191525465ffffffffffff60405191831c168152f35b6001600160401b0381116101b35760051b60200190565b81601f8201121561018557803591610d8c83610d5e565b92610d9a60405194856101ee565b808452602092838086019260051b820101928311610185578301905b828210610dc4575050505090565b81358152908301908301610db6565b9080601f8301121561018557813590610deb82610d5e565b92610df960405194856101ee565b828452602092838086019160051b8301019280841161018557848301915b848310610e275750505050505090565b82356001600160401b038111610185578691610e488484809489010161072c565b815201920191610e17565b34610185576080366003190112610185576001600160401b036004358181116101855736602382011215610185578060040135610e8f81610d5e565b91610e9d60405193846101ee565b81835260209160248385019160051b8301019136831161018557602401905b828210610f0957858560243582811161018557610edd903690600401610d75565b60443592831161018557610ef8610f07933690600401610dd3565b90610f01610a01565b9261134d565b005b8380918335610f178161030a565b815201910190610ebc565b34610185576000366003190112610185576040517f00000000000000000000000000000000000000000000000000000000000000006001600160a01b03168152602090f35b9181601f84011215610185578235916001600160401b038311610185576020808501948460051b01011161018557565b346101855760a036600319011261018557610fb360043561030a565b610fbe60243561030a565b6001600160401b0360443581811161018557610fde903690600401610f67565b505060643581811161018557610ff8903690600401610f67565b505060843590811161018557611012903690600401610326565b505060405163bc197c8160e01b8152602090f35b3461018557600036600319011261018557604051631aab3f0d60e11b8152306004820152600060248201526020816044817f00000000000000000000000000000000000000000000000000000000000000006001600160a01b03165afa801561061f576102d09160009161090a57506040519081529081906020820190565b6110ae36610b28565b6000805160206120f883398151915254919290916001600160a01b03919060501c8216611130576110de81611fc6565b1691823b1561018557611113926000928360405180968195829463064acaab60e11b8452602060048501526024840191611899565b03925af1801561061f5761112357005b80610613610f07926101a0565b60405162dc149f60e41b8152600490fd5b6020366003190112610185576111556103fe565b337f00000000000000000000000000000000000000000000000000000000000000006001600160a01b03161415806111c9575b610624576000805160206120f883398151915290815469ffffffffffff000000004260201b169160e01c9069ffffffffffffffffffff191617179055600080f35b5030331415611188565b346101855760a0366003190112610185576111ef60043561030a565b6111fa60243561030a565b6084356001600160401b03811161018557611219903690600401610326565b505060405163f23a6e6160e01b8152602090f35b63ffffffff60e01b166000527f439ffe7df606b78489639bc0b827913bd09e1246fa6802968a5b3694c53e0dda602052604060002090565b600061127b81356001600160e01b03191661122d565b5460601c337f00000000000000000000000000000000000000000000000000000000000000006001600160a01b03161415806112cf575b61062457818091368280378136915af43d82803e15610ab5573d90f35b506112d8611e30565b156112b2565b600211156112e857565b634e487b7160e01b600052602160045260246000fd5b600019811461130d5760010190565b634e487b7160e01b600052601160045260246000fd5b80518210156113375760209160051b010190565b634e487b7160e01b600052603260045260246000fd5b92909190337f00000000000000000000000000000000000000000000000000000000000000006001600160a01b0316141580611420575b6106245760005b84518110156114195761139d826112de565b816113f8576113db6113bf6113b28388611323565b516001600160a01b031690565b6113c98387611323565b516113d48487611323565b519161203c565b90156113f057506113eb906112fe565b61138b565b602081519101fd5b6113db6114086113b28388611323565b6114128386611323565b5190612067565b5050505050565b5061142c610ae2611e30565b611384565b906004116101855790600490565b909291928360041161018557831161018557600401916003190190565b906024116101855760100190601490565b906058116101855760380190602090565b906024116101855760040190602090565b906038116101855760240190601490565b90600a116101855760040190600690565b9060101161018557600a0190600690565b90939293848311610185578411610185578101920390565b6001600160e01b031990358181169392600481106114f757505050565b60040360031b82901b16169150565b90816020910312610185575190565b606080825282516001600160a01b031690820152919392916040916115db90602081015160808401528381015161155a610160918260a08701526101c0860190610260565b906115c861157a606085015193605f1994858983030160c08a0152610260565b608085015160e088015260a085015192610100938489015260c08601519061012091828a015260e08701519461014095868b0152870151908901528501518488830301610180890152610260565b92015190848303016101a0850152610260565b9460208201520152565b6040513d6000823e3d90fd5b6001600160a01b03939260009290918391907f0000000000000000000000000000000000000000000000000000000000000000871633036118395760049081359788610144810135019280602485019401356000805160206120f883398151915254946116676116618383611431565b906114da565b9b6001600160e01b0319808e16908161171c57505050899a9b50611696826020999a9b9594936116ad9361143f565b9660501c965b858c8061170d575b505036916106e6565b6101408501526116d1604051998a9788968794633a871cdd60e01b86528501611515565b0393165af191821561061f5761074793926116ed575b50612091565b61170691925060203d81116109315761092381836101ee565b90386116e7565b81808092335af150858c6116a4565b9199509197969594939c8660e01b161615156000146117465760405163fc2f51c560e01b81528c90fd5b90899a9b91600160e09b95969798999a9b1b81146000146117e557506117876117826116618b606460209c9d0135016024868201359101611431565b61122d565b60018101549099906001600160a01b031696848816156117da575b50816116ad926117b19261143f565b995460d081901b6001600160d01b03191660709190911b65ffffffffffff60a01b16179961169c565b60501c9650816117a2565b9198979095509250600160e11b0361182b576118216116ad948a9361181c6116618a606460209c01350160248d8201359101611431565b61190e565b919992969161169c565b505050505050505050600190565b604051636b31ba1560e11b8152600490fd5b6bffffffffffffffffffffffff19903581811693926014811061186d57505050565b60140360031b82901b16169150565b35906020811061188a575090565b6000199060200360031b1b1690565b908060209392818452848401376000828201840152601f01601f1916010190565b604090610747949281528160208201520191611899565b6001600160d01b031990358181169392600681106118ee57505050565b60060360031b82901b16169150565b916020610747938181520191611899565b9061193a61192e611928611922868561145c565b9061184b565b60601c90565b6001600160a01b031690565b9361194e611948858461146d565b9061187c565b60588301607882019461196961194887856058018a896114c2565b96611a7261197a611948838961147e565b61198a611928611922858b61148f565b99611a186119993689896106e6565b8051602091820120604080517f3ce406685c1b3551d706d85a68afdaa49ac4e07b451ad9b8ff8b58c3ee9641768185019081526001600160e01b03198b169282019290925260608101969096526001600160a01b039e909e16608086015260a08086019190915284529b8c93611a1060c0826101ee565b519020611be9565b6000805160206120f883398151915254909190611a5490611a449060501c6001600160a01b031661192e565b9189019b60788d0190878d6114c2565b60405163199ed7c960e11b81529586948593849391600485016118ba565b03915afa92831561061f57611782611ab8611b789561052794600091611bcc575b50611ab1611aa1878d61147e565b6001600160a01b0319929161187c565b1690612091565b9a898b016078019a85036077190199611b6890611b58611af8611aed611ae7611ae18b866114a0565b906118d1565b60d01c90565b65ffffffffffff1690565b97611b2f61192e611928611922611b18611aed611ae7611ae1888b6114b1565b94611b29611928611922838b61148f565b9761145c565b94611b49611b3b61020f565b65ffffffffffff909b168b52565b89019065ffffffffffff169052565b6001600160a01b03166040870152565b6001600160a01b03166060850152565b6001600160a01b03871691823b1561018557611bae926000928360405180968195829463064acaab60e11b8452600484016118fd565b03925af1801561061f57611bbf5750565b8061061361021c926101a0565b611be391508d803d106109315761092381836101ee565b38611a93565b7f00000000000000000000000000000000000000000000000000000000000000007f000000000000000000000000000000000000000000000000000000000000000030147f000000000000000000000000000000000000000000000000000000000000000046141615611c76575b671901000000000000600052601a52603a526042601820906000603a52565b5060a06040517f8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f81527f000000000000000000000000000000000000000000000000000000000000000060208201527f0000000000000000000000000000000000000000000000000000000000000000604082015246606082015230608082015220611c57565b6000805160206120f883398151915254611d4a93602093909291611d2c9060501c6001600160a01b031661192e565b916040519586948593849363199ed7c960e11b8552600485016118ba565b03915afa801561061f57611d6691600091611dc1575b50612013565b9165ffffffffffff908142911611611db15742911610611da4576001600160a01b0316611d9857630b135d3f60e11b90565b6001600160e01b031990565b506001600160e01b031990565b506001600160e01b031992915050565b611dd9915060203d81116109315761092381836101ee565b38611d60565b90816020910312610185575180151581036101855790565b6001600160a01b0390911681526040602082018190528101829052606091806000848401376000828201840152601f01601f1916010190565b6000805160206120f883398151915254611e559060501c6001600160a01b031661192e565b6040519081639ea9bd5960e01b9182825260209384918180611e7b363360048401611df7565b03915afa90811561061f57600091611fa9575b50611fa257611ea86000356001600160e01b03191661122d565b6001810154909190611ec2906001600160a01b031661192e565b916001600160a01b03831615908115611f66575b8115611f42575b5015611eeb57505050600090565b829060405192839182528180611f05363360048401611df7565b03915afa91821561061f57600092611f1c57505090565b6107479250803d10611f3b575b611f3381836101ee565b810190611ddf565b503d611f29565b54611f55915065ffffffffffff16611aed565b65ffffffffffff4291161138611edd565b905065ffffffffffff611f86611aed835465ffffffffffff9060301c1690565b168015159081611f98575b5090611ed6565b9050421138611f91565b5050600190565b611fc09150833d8511611f3b57611f3381836101ee565b38611e8e565b6000805160206120f883398151915280547fffff0000000000000000000000000000000000000000ffffffffffffffffffff1660509290921b600160501b600160f01b0316919091179055565b8065ffffffffffff91828160a01c16928315600114612034575b5060d01c92565b92503861202d565b916000928392602083519301915af1903d604051906020818301016040528082526000602083013e90565b6000918291602082519201905af4903d604051906020818301016040528082526000602083013e90565b8082186001600160a01b0316156001146120ac575050600190565b65ffffffffffff60a01b828116828216818118918111919091028082189465ffffffffffff60a01b1994851694169291146120ef575b5081811190821802181790565b9250386120e256fe439ffe7df606b78489639bc0b827913bd09e1246fa6802968a5b3694c53e0dd9";

type KernelConstructorParams =
  | [signer?: Signer]
  | ConstructorParameters<typeof ContractFactory>;

const isSuperArgs = (
  xs: KernelConstructorParams
): xs is ConstructorParameters<typeof ContractFactory> => xs.length > 1;

export class Kernel__factory extends ContractFactory {
  constructor(...args: KernelConstructorParams) {
    if (isSuperArgs(args)) {
      super(...args);
    } else {
      super(_abi, _bytecode, args[0]);
    }
  }

  override deploy(
    _entryPoint: PromiseOrValue<string>,
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): Promise<Kernel> {
    return super.deploy(_entryPoint, overrides || {}) as Promise<Kernel>;
  }
  override getDeployTransaction(
    _entryPoint: PromiseOrValue<string>,
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): TransactionRequest {
    return super.getDeployTransaction(_entryPoint, overrides || {});
  }
  override attach(address: string): Kernel {
    return super.attach(address) as Kernel;
  }
  override connect(signer: Signer): Kernel__factory {
    return super.connect(signer) as Kernel__factory;
  }

  static readonly bytecode = _bytecode;
  static readonly abi = _abi;
  static createInterface(): KernelInterface {
    return new utils.Interface(_abi) as KernelInterface;
  }
  static connect(address: string, signerOrProvider: Signer | Provider): Kernel {
    return new Contract(address, _abi, signerOrProvider) as Kernel;
  }
}