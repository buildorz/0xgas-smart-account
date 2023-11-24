/* Autogenerated file. Do not edit manually. */
/* tslint:disable */
/* eslint-disable */
import { Signer, utils, Contract, ContractFactory, Overrides } from "ethers";
import type { Provider, TransactionRequest } from "@ethersproject/providers";
import type { PromiseOrValue } from "../common";
import type { KernelFactory, KernelFactoryInterface } from "../KernelFactory";

const _abi = [
  {
    inputs: [
      {
        internalType: "address",
        name: "_owner",
        type: "address",
      },
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
    name: "DeploymentFailed",
    type: "error",
  },
  {
    inputs: [],
    name: "NewOwnerIsZeroAddress",
    type: "error",
  },
  {
    inputs: [],
    name: "NoHandoverRequest",
    type: "error",
  },
  {
    inputs: [],
    name: "SaltDoesNotStartWithCaller",
    type: "error",
  },
  {
    inputs: [],
    name: "Unauthorized",
    type: "error",
  },
  {
    anonymous: false,
    inputs: [
      {
        indexed: true,
        internalType: "address",
        name: "proxy",
        type: "address",
      },
      {
        indexed: true,
        internalType: "address",
        name: "implementation",
        type: "address",
      },
    ],
    name: "Deployed",
    type: "event",
  },
  {
    anonymous: false,
    inputs: [
      {
        indexed: true,
        internalType: "address",
        name: "pendingOwner",
        type: "address",
      },
    ],
    name: "OwnershipHandoverCanceled",
    type: "event",
  },
  {
    anonymous: false,
    inputs: [
      {
        indexed: true,
        internalType: "address",
        name: "pendingOwner",
        type: "address",
      },
    ],
    name: "OwnershipHandoverRequested",
    type: "event",
  },
  {
    anonymous: false,
    inputs: [
      {
        indexed: true,
        internalType: "address",
        name: "oldOwner",
        type: "address",
      },
      {
        indexed: true,
        internalType: "address",
        name: "newOwner",
        type: "address",
      },
    ],
    name: "OwnershipTransferred",
    type: "event",
  },
  {
    inputs: [
      {
        internalType: "uint32",
        name: "unstakeDelaySec",
        type: "uint32",
      },
    ],
    name: "addStake",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [],
    name: "cancelOwnershipHandover",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "pendingOwner",
        type: "address",
      },
    ],
    name: "completeOwnershipHandover",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "_implementation",
        type: "address",
      },
      {
        internalType: "bytes",
        name: "_data",
        type: "bytes",
      },
      {
        internalType: "uint256",
        name: "_index",
        type: "uint256",
      },
    ],
    name: "createAccount",
    outputs: [
      {
        internalType: "address",
        name: "proxy",
        type: "address",
      },
    ],
    stateMutability: "payable",
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
        internalType: "bytes",
        name: "_data",
        type: "bytes",
      },
      {
        internalType: "uint256",
        name: "_index",
        type: "uint256",
      },
    ],
    name: "getAccountAddress",
    outputs: [
      {
        internalType: "address",
        name: "",
        type: "address",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "initCodeHash",
    outputs: [
      {
        internalType: "bytes32",
        name: "result",
        type: "bytes32",
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
    ],
    name: "isAllowedImplementation",
    outputs: [
      {
        internalType: "bool",
        name: "",
        type: "bool",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "owner",
    outputs: [
      {
        internalType: "address",
        name: "result",
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
        name: "pendingOwner",
        type: "address",
      },
    ],
    name: "ownershipHandoverExpiresAt",
    outputs: [
      {
        internalType: "uint256",
        name: "result",
        type: "uint256",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "ownershipHandoverValidFor",
    outputs: [
      {
        internalType: "uint64",
        name: "",
        type: "uint64",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "bytes32",
        name: "salt",
        type: "bytes32",
      },
    ],
    name: "predictDeterministicAddress",
    outputs: [
      {
        internalType: "address",
        name: "predicted",
        type: "address",
      },
    ],
    stateMutability: "view",
    type: "function",
  },
  {
    inputs: [],
    name: "renounceOwnership",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [],
    name: "requestOwnershipHandover",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "contract IEntryPoint",
        name: "_entryPoint",
        type: "address",
      },
    ],
    name: "setEntryPoint",
    outputs: [],
    stateMutability: "nonpayable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "_implementation",
        type: "address",
      },
      {
        internalType: "bool",
        name: "_allow",
        type: "bool",
      },
    ],
    name: "setImplementation",
    outputs: [],
    stateMutability: "nonpayable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address",
        name: "newOwner",
        type: "address",
      },
    ],
    name: "transferOwnership",
    outputs: [],
    stateMutability: "payable",
    type: "function",
  },
  {
    inputs: [],
    name: "unlockStake",
    outputs: [],
    stateMutability: "nonpayable",
    type: "function",
  },
  {
    inputs: [
      {
        internalType: "address payable",
        name: "withdrawAddress",
        type: "address",
      },
    ],
    name: "withdrawStake",
    outputs: [],
    stateMutability: "nonpayable",
    type: "function",
  },
] as const;

const _bytecode =
  "0x6080346100b257601f610b2d38819003918201601f19168301916001600160401b038311848410176100b75780849260409485528339810103126100b25780516001600160a01b0391828216918290036100b257602001519182168092036100b25780638b78c6d8195560007f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e08180a3600080546001600160a01b031916919091179055604051610a5f90816100ce8239f35b600080fd5b634e487b7160e01b600052604160045260246000fdfe6040608081526004908136101561001557600080fd5b600091823560e01c9081630396cb60146107d45781632569296214610789578163296601cd1461059d5781634d6cb7001461052b5781635414dff0146104fa57816354d1f13d146104b4578163584465f2146104745781636544c82814610436578163715018a6146103f05781638da5cb5b146103c3578163b0d691fe1461039b578163bb30a9741461034557838263bb9fe6bf146102ec578263c23a5cea1461026157508163d7533f0214610243578163db4c545e14610219578163f04e283e14610199578163f2fde38b1461012c575063fee81cf4146100f657600080fd5b3461012857602036600319011261012857602091610112610845565b9063389a75e1600c525281600c20549051908152f35b5080fd5b8390602036600319011261012857610142610845565b9061014b61088e565b8160601b1561018e575060018060a01b0316638b78c6d8198181547f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e08580a35580f35b637448fbae8352601cfd5b83906020366003190112610128576101af610845565b906101b861088e565b63389a75e1600c528183526020600c20908154421161020e575082905560018060a01b0316638b78c6d8198181547f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e08580a35580f35b636f5e88188452601cfd5b5050346101285781600319360112610128576020906089601361023a6108d8565b01209051908152f35b505034610128578160031936011261012857602090516202a3008152f35b809184346102e85760203660031901126102e85781356001600160a01b0381811693918490036102e45761029361088e565b84541692833b156102e45760248592838551968794859363611d2e7560e11b85528401525af19081156102db57506102c85750f35b6102d190610a13565b6102d85780f35b80fd5b513d84823e3d90fd5b8480fd5b5050fd5b809184346102e857826003193601126102e85761030761088e565b82546001600160a01b031691823b1561034057815163bb9fe6bf60e01b81529284918491829084905af19081156102db57506102c85750f35b505050fd5b50503461012857806003193601126101285761035f610845565b90602435918215158093036103975761037661088e565b60018060a01b03168352600160205282209060ff8019835416911617905580f35b8380fd5b505034610128578160031936011261012857905490516001600160a01b039091168152602090f35b505034610128578160031936011261012857638b78c6d8195490516001600160a01b039091168152602090f35b83806003193601126102d85761040461088e565b80638b78c6d8198181547f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e08280a35580f35b5050346101285760203660031901126101285760209160ff9082906001600160a01b03610461610845565b1681526001855220541690519015158152f35b83903461012857602036600319011261012857356001600160a01b03811690819003610128576104a261088e565b81546001600160a01b03191617815580f35b83806003193601126102d85763389a75e1600c52338152806020600c2055337ffa7b8eab7da67f412cc9575ed43464468f9bfbae89d1675917346ca6d8fe3c928280a280f35b8284346102d85760203660031901126102d8575061051a602092356108ab565b90516001600160a01b039091168152f35b8284346102d857816003193601126102d85782359067ffffffffffffffff82116102d857506bffffffffffffffffffffffff61056f60209461051a93369101610860565b6105948580518381948a830196873781016024358a8201520388810184520182610a3d565b519020166108ab565b828460603660031901126102d8576105b3610845565b9160243567ffffffffffffffff8111610785576105d39036908601610860565b9360018060a01b039384821681526020966001885260ff858320541615610730576bffffffffffffffffffffffff8551898101908987833761062988828d8d82019060443590820152038d810184520182610a3d565b5190201696331560011715610724576106406108d8565b90601382019860898a2060ff86536035523060601b600152806015526055852099856035528a3b15610678575b8b8b8b8b5191168152f35b856089929394959697989b50f597881561071857918185939284938884527f360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc8d85015289840137870190348a5af1156106fe57507f09e48df7857bd0c1e0d31bb8a85d42cf1874817895f171c917f6ee2cea73ec20818692a3848080808080808061066d565b3d1561070d57503d81803e3d90fd5b63301164258252601cfd5b8363301164258652601cfd5b50632f6348368252601cfd5b845162461bcd60e51b8152908101889052602960248201527f4b65726e656c466163746f72793a20696d706c656d656e746174696f6e206e6f6044820152681d08185b1b1bddd95960ba1b6064820152608490fd5b8280fd5b83806003193601126102d85763389a75e1600c523381526202a30042016020600c2055337fdbf36a107da19e49527a7176a1babf963b4b0ff8cde35ee35d6cd8f1f9ac7e1d8280a280f35b91905060203660031901126107855782823563ffffffff8116809103610128576107fc61088e565b81546001600160a01b031693843b156107855760249084519586938492621cb65b60e51b845283015234905af19081156102db5750610839575080f35b61084290610a13565b80f35b600435906001600160a01b038216820361085b57565b600080fd5b9181601f8401121561085b5782359167ffffffffffffffff831161085b576020838186019501011161085b57565b638b78c6d81954330361089d57565b6382b429006000526004601cfd5b608960136108b76108d8565b012060ff6000536035523060601b6001526015526055600020906000603552565b604051903060701c1561097c57666052573d6000fd607b8301527f3d356020355560408036111560525736038060403d373d3d355af43d6000803e60748301527f3735a920a3ca505d382bbc545af43d6000803e6052573d6000fd5b3d6000f35b60548301527f14605757363d3d37363d7f360894a13ba1a3210667c828492db98dca3e2076cc60348301523060148301526c607f3d8160093d39f33d3d33738252565b66604c573d6000fd60758301527f3d3560203555604080361115604c5736038060403d373d3d355af43d6000803e606e8301527f3735a920a3ca505d382bbc545af43d6000803e604c573d6000fd5b3d6000f35b604e8301527f14605157363d3d37363d7f360894a13ba1a3210667c828492db98dca3e2076cc602e83015230600e8301526c60793d8160093d39f33d3d336d8252565b67ffffffffffffffff8111610a2757604052565b634e487b7160e01b600052604160045260246000fd5b90601f8019910116810190811067ffffffffffffffff821117610a275760405256";

type KernelFactoryConstructorParams =
  | [signer?: Signer]
  | ConstructorParameters<typeof ContractFactory>;

const isSuperArgs = (
  xs: KernelFactoryConstructorParams
): xs is ConstructorParameters<typeof ContractFactory> => xs.length > 1;

export class KernelFactory__factory extends ContractFactory {
  constructor(...args: KernelFactoryConstructorParams) {
    if (isSuperArgs(args)) {
      super(...args);
    } else {
      super(_abi, _bytecode, args[0]);
    }
  }

  override deploy(
    _owner: PromiseOrValue<string>,
    _entryPoint: PromiseOrValue<string>,
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): Promise<KernelFactory> {
    return super.deploy(
      _owner,
      _entryPoint,
      overrides || {}
    ) as Promise<KernelFactory>;
  }
  override getDeployTransaction(
    _owner: PromiseOrValue<string>,
    _entryPoint: PromiseOrValue<string>,
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): TransactionRequest {
    return super.getDeployTransaction(_owner, _entryPoint, overrides || {});
  }
  override attach(address: string): KernelFactory {
    return super.attach(address) as KernelFactory;
  }
  override connect(signer: Signer): KernelFactory__factory {
    return super.connect(signer) as KernelFactory__factory;
  }

  static readonly bytecode = _bytecode;
  static readonly abi = _abi;
  static createInterface(): KernelFactoryInterface {
    return new utils.Interface(_abi) as KernelFactoryInterface;
  }
  static connect(
    address: string,
    signerOrProvider: Signer | Provider
  ): KernelFactory {
    return new Contract(address, _abi, signerOrProvider) as KernelFactory;
  }
}
