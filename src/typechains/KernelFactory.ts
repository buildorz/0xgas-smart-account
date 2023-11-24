/* Autogenerated file. Do not edit manually. */
/* tslint:disable */
/* eslint-disable */
import type {
  BaseContract,
  BigNumber,
  BigNumberish,
  BytesLike,
  CallOverrides,
  ContractTransaction,
  Overrides,
  PayableOverrides,
  PopulatedTransaction,
  Signer,
  utils,
} from "ethers";
import type {
  FunctionFragment,
  Result,
  EventFragment,
} from "@ethersproject/abi";
import type { Listener, Provider } from "@ethersproject/providers";
import type {
  TypedEventFilter,
  TypedEvent,
  TypedListener,
  OnEvent,
  PromiseOrValue,
} from "./common";

export interface KernelFactoryInterface extends utils.Interface {
  functions: {
    "addStake(uint32)": FunctionFragment;
    "cancelOwnershipHandover()": FunctionFragment;
    "completeOwnershipHandover(address)": FunctionFragment;
    "createAccount(address,bytes,uint256)": FunctionFragment;
    "entryPoint()": FunctionFragment;
    "getAccountAddress(bytes,uint256)": FunctionFragment;
    "initCodeHash()": FunctionFragment;
    "isAllowedImplementation(address)": FunctionFragment;
    "owner()": FunctionFragment;
    "ownershipHandoverExpiresAt(address)": FunctionFragment;
    "ownershipHandoverValidFor()": FunctionFragment;
    "predictDeterministicAddress(bytes32)": FunctionFragment;
    "renounceOwnership()": FunctionFragment;
    "requestOwnershipHandover()": FunctionFragment;
    "setEntryPoint(address)": FunctionFragment;
    "setImplementation(address,bool)": FunctionFragment;
    "transferOwnership(address)": FunctionFragment;
    "unlockStake()": FunctionFragment;
    "withdrawStake(address)": FunctionFragment;
  };

  getFunction(
    nameOrSignatureOrTopic:
      | "addStake"
      | "cancelOwnershipHandover"
      | "completeOwnershipHandover"
      | "createAccount"
      | "entryPoint"
      | "getAccountAddress"
      | "initCodeHash"
      | "isAllowedImplementation"
      | "owner"
      | "ownershipHandoverExpiresAt"
      | "ownershipHandoverValidFor"
      | "predictDeterministicAddress"
      | "renounceOwnership"
      | "requestOwnershipHandover"
      | "setEntryPoint"
      | "setImplementation"
      | "transferOwnership"
      | "unlockStake"
      | "withdrawStake"
  ): FunctionFragment;

  encodeFunctionData(
    functionFragment: "addStake",
    values: [PromiseOrValue<BigNumberish>]
  ): string;
  encodeFunctionData(
    functionFragment: "cancelOwnershipHandover",
    values?: undefined
  ): string;
  encodeFunctionData(
    functionFragment: "completeOwnershipHandover",
    values: [PromiseOrValue<string>]
  ): string;
  encodeFunctionData(
    functionFragment: "createAccount",
    values: [
      PromiseOrValue<string>,
      PromiseOrValue<BytesLike>,
      PromiseOrValue<BigNumberish>
    ]
  ): string;
  encodeFunctionData(
    functionFragment: "entryPoint",
    values?: undefined
  ): string;
  encodeFunctionData(
    functionFragment: "getAccountAddress",
    values: [PromiseOrValue<BytesLike>, PromiseOrValue<BigNumberish>]
  ): string;
  encodeFunctionData(
    functionFragment: "initCodeHash",
    values?: undefined
  ): string;
  encodeFunctionData(
    functionFragment: "isAllowedImplementation",
    values: [PromiseOrValue<string>]
  ): string;
  encodeFunctionData(functionFragment: "owner", values?: undefined): string;
  encodeFunctionData(
    functionFragment: "ownershipHandoverExpiresAt",
    values: [PromiseOrValue<string>]
  ): string;
  encodeFunctionData(
    functionFragment: "ownershipHandoverValidFor",
    values?: undefined
  ): string;
  encodeFunctionData(
    functionFragment: "predictDeterministicAddress",
    values: [PromiseOrValue<BytesLike>]
  ): string;
  encodeFunctionData(
    functionFragment: "renounceOwnership",
    values?: undefined
  ): string;
  encodeFunctionData(
    functionFragment: "requestOwnershipHandover",
    values?: undefined
  ): string;
  encodeFunctionData(
    functionFragment: "setEntryPoint",
    values: [PromiseOrValue<string>]
  ): string;
  encodeFunctionData(
    functionFragment: "setImplementation",
    values: [PromiseOrValue<string>, PromiseOrValue<boolean>]
  ): string;
  encodeFunctionData(
    functionFragment: "transferOwnership",
    values: [PromiseOrValue<string>]
  ): string;
  encodeFunctionData(
    functionFragment: "unlockStake",
    values?: undefined
  ): string;
  encodeFunctionData(
    functionFragment: "withdrawStake",
    values: [PromiseOrValue<string>]
  ): string;

  decodeFunctionResult(functionFragment: "addStake", data: BytesLike): Result;
  decodeFunctionResult(
    functionFragment: "cancelOwnershipHandover",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "completeOwnershipHandover",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "createAccount",
    data: BytesLike
  ): Result;
  decodeFunctionResult(functionFragment: "entryPoint", data: BytesLike): Result;
  decodeFunctionResult(
    functionFragment: "getAccountAddress",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "initCodeHash",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "isAllowedImplementation",
    data: BytesLike
  ): Result;
  decodeFunctionResult(functionFragment: "owner", data: BytesLike): Result;
  decodeFunctionResult(
    functionFragment: "ownershipHandoverExpiresAt",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "ownershipHandoverValidFor",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "predictDeterministicAddress",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "renounceOwnership",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "requestOwnershipHandover",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "setEntryPoint",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "setImplementation",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "transferOwnership",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "unlockStake",
    data: BytesLike
  ): Result;
  decodeFunctionResult(
    functionFragment: "withdrawStake",
    data: BytesLike
  ): Result;

  events: {
    "Deployed(address,address)": EventFragment;
    "OwnershipHandoverCanceled(address)": EventFragment;
    "OwnershipHandoverRequested(address)": EventFragment;
    "OwnershipTransferred(address,address)": EventFragment;
  };

  getEvent(nameOrSignatureOrTopic: "Deployed"): EventFragment;
  getEvent(nameOrSignatureOrTopic: "OwnershipHandoverCanceled"): EventFragment;
  getEvent(nameOrSignatureOrTopic: "OwnershipHandoverRequested"): EventFragment;
  getEvent(nameOrSignatureOrTopic: "OwnershipTransferred"): EventFragment;
}

export interface DeployedEventObject {
  proxy: string;
  implementation: string;
}
export type DeployedEvent = TypedEvent<[string, string], DeployedEventObject>;

export type DeployedEventFilter = TypedEventFilter<DeployedEvent>;

export interface OwnershipHandoverCanceledEventObject {
  pendingOwner: string;
}
export type OwnershipHandoverCanceledEvent = TypedEvent<
  [string],
  OwnershipHandoverCanceledEventObject
>;

export type OwnershipHandoverCanceledEventFilter =
  TypedEventFilter<OwnershipHandoverCanceledEvent>;

export interface OwnershipHandoverRequestedEventObject {
  pendingOwner: string;
}
export type OwnershipHandoverRequestedEvent = TypedEvent<
  [string],
  OwnershipHandoverRequestedEventObject
>;

export type OwnershipHandoverRequestedEventFilter =
  TypedEventFilter<OwnershipHandoverRequestedEvent>;

export interface OwnershipTransferredEventObject {
  oldOwner: string;
  newOwner: string;
}
export type OwnershipTransferredEvent = TypedEvent<
  [string, string],
  OwnershipTransferredEventObject
>;

export type OwnershipTransferredEventFilter =
  TypedEventFilter<OwnershipTransferredEvent>;

export interface KernelFactory extends BaseContract {
  connect(signerOrProvider: Signer | Provider | string): this;
  attach(addressOrName: string): this;
  deployed(): Promise<this>;

  interface: KernelFactoryInterface;

  queryFilter<TEvent extends TypedEvent>(
    event: TypedEventFilter<TEvent>,
    fromBlockOrBlockhash?: string | number | undefined,
    toBlock?: string | number | undefined
  ): Promise<Array<TEvent>>;

  listeners<TEvent extends TypedEvent>(
    eventFilter?: TypedEventFilter<TEvent>
  ): Array<TypedListener<TEvent>>;
  listeners(eventName?: string): Array<Listener>;
  removeAllListeners<TEvent extends TypedEvent>(
    eventFilter: TypedEventFilter<TEvent>
  ): this;
  removeAllListeners(eventName?: string): this;
  off: OnEvent<this>;
  on: OnEvent<this>;
  once: OnEvent<this>;
  removeListener: OnEvent<this>;

  functions: {
    addStake(
      unstakeDelaySec: PromiseOrValue<BigNumberish>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    cancelOwnershipHandover(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    completeOwnershipHandover(
      pendingOwner: PromiseOrValue<string>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    createAccount(
      _implementation: PromiseOrValue<string>,
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    entryPoint(overrides?: CallOverrides): Promise<[string]>;

    getAccountAddress(
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: CallOverrides
    ): Promise<[string]>;

    initCodeHash(
      overrides?: CallOverrides
    ): Promise<[string] & { result: string }>;

    isAllowedImplementation(
      arg0: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<[boolean]>;

    owner(overrides?: CallOverrides): Promise<[string] & { result: string }>;

    ownershipHandoverExpiresAt(
      pendingOwner: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<[BigNumber] & { result: BigNumber }>;

    ownershipHandoverValidFor(overrides?: CallOverrides): Promise<[BigNumber]>;

    predictDeterministicAddress(
      salt: PromiseOrValue<BytesLike>,
      overrides?: CallOverrides
    ): Promise<[string] & { predicted: string }>;

    renounceOwnership(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    requestOwnershipHandover(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    setEntryPoint(
      _entryPoint: PromiseOrValue<string>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    setImplementation(
      _implementation: PromiseOrValue<string>,
      _allow: PromiseOrValue<boolean>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    transferOwnership(
      newOwner: PromiseOrValue<string>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    unlockStake(
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;

    withdrawStake(
      withdrawAddress: PromiseOrValue<string>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<ContractTransaction>;
  };

  addStake(
    unstakeDelaySec: PromiseOrValue<BigNumberish>,
    overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  cancelOwnershipHandover(
    overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  completeOwnershipHandover(
    pendingOwner: PromiseOrValue<string>,
    overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  createAccount(
    _implementation: PromiseOrValue<string>,
    _data: PromiseOrValue<BytesLike>,
    _index: PromiseOrValue<BigNumberish>,
    overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  entryPoint(overrides?: CallOverrides): Promise<string>;

  getAccountAddress(
    _data: PromiseOrValue<BytesLike>,
    _index: PromiseOrValue<BigNumberish>,
    overrides?: CallOverrides
  ): Promise<string>;

  initCodeHash(overrides?: CallOverrides): Promise<string>;

  isAllowedImplementation(
    arg0: PromiseOrValue<string>,
    overrides?: CallOverrides
  ): Promise<boolean>;

  owner(overrides?: CallOverrides): Promise<string>;

  ownershipHandoverExpiresAt(
    pendingOwner: PromiseOrValue<string>,
    overrides?: CallOverrides
  ): Promise<BigNumber>;

  ownershipHandoverValidFor(overrides?: CallOverrides): Promise<BigNumber>;

  predictDeterministicAddress(
    salt: PromiseOrValue<BytesLike>,
    overrides?: CallOverrides
  ): Promise<string>;

  renounceOwnership(
    overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  requestOwnershipHandover(
    overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  setEntryPoint(
    _entryPoint: PromiseOrValue<string>,
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  setImplementation(
    _implementation: PromiseOrValue<string>,
    _allow: PromiseOrValue<boolean>,
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  transferOwnership(
    newOwner: PromiseOrValue<string>,
    overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  unlockStake(
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  withdrawStake(
    withdrawAddress: PromiseOrValue<string>,
    overrides?: Overrides & { from?: PromiseOrValue<string> }
  ): Promise<ContractTransaction>;

  callStatic: {
    addStake(
      unstakeDelaySec: PromiseOrValue<BigNumberish>,
      overrides?: CallOverrides
    ): Promise<void>;

    cancelOwnershipHandover(overrides?: CallOverrides): Promise<void>;

    completeOwnershipHandover(
      pendingOwner: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<void>;

    createAccount(
      _implementation: PromiseOrValue<string>,
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: CallOverrides
    ): Promise<string>;

    entryPoint(overrides?: CallOverrides): Promise<string>;

    getAccountAddress(
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: CallOverrides
    ): Promise<string>;

    initCodeHash(overrides?: CallOverrides): Promise<string>;

    isAllowedImplementation(
      arg0: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<boolean>;

    owner(overrides?: CallOverrides): Promise<string>;

    ownershipHandoverExpiresAt(
      pendingOwner: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<BigNumber>;

    ownershipHandoverValidFor(overrides?: CallOverrides): Promise<BigNumber>;

    predictDeterministicAddress(
      salt: PromiseOrValue<BytesLike>,
      overrides?: CallOverrides
    ): Promise<string>;

    renounceOwnership(overrides?: CallOverrides): Promise<void>;

    requestOwnershipHandover(overrides?: CallOverrides): Promise<void>;

    setEntryPoint(
      _entryPoint: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<void>;

    setImplementation(
      _implementation: PromiseOrValue<string>,
      _allow: PromiseOrValue<boolean>,
      overrides?: CallOverrides
    ): Promise<void>;

    transferOwnership(
      newOwner: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<void>;

    unlockStake(overrides?: CallOverrides): Promise<void>;

    withdrawStake(
      withdrawAddress: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<void>;
  };

  filters: {
    "Deployed(address,address)"(
      proxy?: PromiseOrValue<string> | null,
      implementation?: PromiseOrValue<string> | null
    ): DeployedEventFilter;
    Deployed(
      proxy?: PromiseOrValue<string> | null,
      implementation?: PromiseOrValue<string> | null
    ): DeployedEventFilter;

    "OwnershipHandoverCanceled(address)"(
      pendingOwner?: PromiseOrValue<string> | null
    ): OwnershipHandoverCanceledEventFilter;
    OwnershipHandoverCanceled(
      pendingOwner?: PromiseOrValue<string> | null
    ): OwnershipHandoverCanceledEventFilter;

    "OwnershipHandoverRequested(address)"(
      pendingOwner?: PromiseOrValue<string> | null
    ): OwnershipHandoverRequestedEventFilter;
    OwnershipHandoverRequested(
      pendingOwner?: PromiseOrValue<string> | null
    ): OwnershipHandoverRequestedEventFilter;

    "OwnershipTransferred(address,address)"(
      oldOwner?: PromiseOrValue<string> | null,
      newOwner?: PromiseOrValue<string> | null
    ): OwnershipTransferredEventFilter;
    OwnershipTransferred(
      oldOwner?: PromiseOrValue<string> | null,
      newOwner?: PromiseOrValue<string> | null
    ): OwnershipTransferredEventFilter;
  };

  estimateGas: {
    addStake(
      unstakeDelaySec: PromiseOrValue<BigNumberish>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    cancelOwnershipHandover(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    completeOwnershipHandover(
      pendingOwner: PromiseOrValue<string>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    createAccount(
      _implementation: PromiseOrValue<string>,
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    entryPoint(overrides?: CallOverrides): Promise<BigNumber>;

    getAccountAddress(
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: CallOverrides
    ): Promise<BigNumber>;

    initCodeHash(overrides?: CallOverrides): Promise<BigNumber>;

    isAllowedImplementation(
      arg0: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<BigNumber>;

    owner(overrides?: CallOverrides): Promise<BigNumber>;

    ownershipHandoverExpiresAt(
      pendingOwner: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<BigNumber>;

    ownershipHandoverValidFor(overrides?: CallOverrides): Promise<BigNumber>;

    predictDeterministicAddress(
      salt: PromiseOrValue<BytesLike>,
      overrides?: CallOverrides
    ): Promise<BigNumber>;

    renounceOwnership(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    requestOwnershipHandover(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    setEntryPoint(
      _entryPoint: PromiseOrValue<string>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    setImplementation(
      _implementation: PromiseOrValue<string>,
      _allow: PromiseOrValue<boolean>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    transferOwnership(
      newOwner: PromiseOrValue<string>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    unlockStake(
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;

    withdrawStake(
      withdrawAddress: PromiseOrValue<string>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<BigNumber>;
  };

  populateTransaction: {
    addStake(
      unstakeDelaySec: PromiseOrValue<BigNumberish>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    cancelOwnershipHandover(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    completeOwnershipHandover(
      pendingOwner: PromiseOrValue<string>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    createAccount(
      _implementation: PromiseOrValue<string>,
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    entryPoint(overrides?: CallOverrides): Promise<PopulatedTransaction>;

    getAccountAddress(
      _data: PromiseOrValue<BytesLike>,
      _index: PromiseOrValue<BigNumberish>,
      overrides?: CallOverrides
    ): Promise<PopulatedTransaction>;

    initCodeHash(overrides?: CallOverrides): Promise<PopulatedTransaction>;

    isAllowedImplementation(
      arg0: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<PopulatedTransaction>;

    owner(overrides?: CallOverrides): Promise<PopulatedTransaction>;

    ownershipHandoverExpiresAt(
      pendingOwner: PromiseOrValue<string>,
      overrides?: CallOverrides
    ): Promise<PopulatedTransaction>;

    ownershipHandoverValidFor(
      overrides?: CallOverrides
    ): Promise<PopulatedTransaction>;

    predictDeterministicAddress(
      salt: PromiseOrValue<BytesLike>,
      overrides?: CallOverrides
    ): Promise<PopulatedTransaction>;

    renounceOwnership(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    requestOwnershipHandover(
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    setEntryPoint(
      _entryPoint: PromiseOrValue<string>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    setImplementation(
      _implementation: PromiseOrValue<string>,
      _allow: PromiseOrValue<boolean>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    transferOwnership(
      newOwner: PromiseOrValue<string>,
      overrides?: PayableOverrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    unlockStake(
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;

    withdrawStake(
      withdrawAddress: PromiseOrValue<string>,
      overrides?: Overrides & { from?: PromiseOrValue<string> }
    ): Promise<PopulatedTransaction>;
  };
}
