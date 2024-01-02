# 使用说明

为了能够使用最新的Agda和PLFA，需要使用ghcup和cabal进行安装。下面是基于Ubuntu的安装过程。

## 硬件需求

安装Agda需要至少4G的内存（不足可以使用交换空间弥补），以及足够的存储空间，否则会在运行中报错。

## 安装ghcup

国外源下载ghcup可能会导致很慢，因此这里使用[ustc源](https://mirrors.ustc.edu.cn/help/ghcup.html)。

**前提准备**

首先应当安装`curl`，`git`，`vim`以便后续使用。

```bash
sudo apt install -y curl git vim
```

在`~`目录下提前创建`.ghcup`文件夹，并在内部创建`config.yaml`文件，添加如下内容：

```yaml
cache: null
downloader: Curl
gpg-setting: null
keep-dirs: null
key-bindings: null
meta-cache: null
meta-mode: null
mirrors: null
no-network: null
no-verify: null
platform-override: null
url-source:
    OwnSource: https://mirrors.ustc.edu.cn/ghcup/ghcup-metadata/ghcup-0.0.7.yaml
verbose: null
```

**安装ghcup**

首先安装必要的包：

```bash
sudo apt install build-essential libffi-dev libffi8ubuntu1 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5
```

然后运行如下命令：

```bash
# Linux, FreeBSD, macOS 用户：在终端中运行如下命令
curl --proto '=https' --tlsv1.2 -sSf https://mirrors.ustc.edu.cn/ghcup/sh/bootstrap-haskell | BOOTSTRAP_HASKELL_YAML=https://mirrors.ustc.edu.cn/ghcup/ghcup-metadata/ghcup-0.0.7.yaml sh
```

接下来按照需求进行一系列选择（本人直接全部选是），选择过后终端会提示安装必要的包，这些包已经安装完成可以直接继续。会等待较长一段时间。

安装完成后，更新环境变量：

```bash
source ~/.bashrc
```

然后使用`ghcup tui`就可以查看当前的HLS,cabal,stack,ghc安装版本。

> 提示： 由于ghcup默认安装的ghc版本更新速度比较快，可以改为官方建议版本，建议到官网https://agda-zh.github.io/PLFA-zh/GettingStarted/查看

## 安装Agda

**前提准备**

我们将使用Cabal进行Agda安装，在此之前我们需要完成一定的前提准备。

首先修改cabal源，找到`~/.cabal/config`，找到官方仓库:

```
repository hackage.haskell.org
  url: http://hackage.haskell.org/
  -- secure: True
  -- root-keys:
  -- keys-threshold: 3
```

改为科大源：

```
repository mirrors.ustc.edu.cn
  url: https://mirrors.ustc.edu.cn/hackage/
  secure: True
```

然后更新:

```bash
cabal update
```

> 不用理会警告

接着安装必要的包：

```bash
sudo apt install zlib1g-dev libncurses5-dev
```

> 新版本已经无需安装Alex,Happy

**安装Agda**

```bash
cabal install Agda
```

需要等待较长的时间，如果安装失败可以尝试回退ghc或者Agda版本。

## PLFA与Agda标准库安装

```bash
git clone --depth 1 --recurse-submodules --shallow-submodules https://github.com/plfa/plfa.github.io plfa
```

命令中的选项中`--recurse-submodules`使得下载包含了Agda标准库。

最后需要告诉Agda如何找到标准库，我们需要两个文件，一个用于制定库的路径`libraries`，另一个用于指定默认载入的库`defaults`。

```bash
mkdir -p ~/.agda
cp ~/plfa/data/dotagda/* ~/.agda
```

此时我们可以正常使用Agda标准库以及PLFA。

## 测试

使用vscode安装`agda-mode`插件后，打开`~/plfa/src`文件夹，任意找到一个markdown文件(后缀为.lagda.md)打开，按`ctrl-c ctrl-l`，如果显示`All Done`则Agda安装成功。

另外可以在其他文件夹尝试调用PLFA内的文件，看是否调用成功。